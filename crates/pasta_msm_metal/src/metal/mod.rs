//! The Metal compute backend (Apple AArch64 only).
//!
//! [`Metal::open`] takes the system default device, compiles
//! [`crate::SHADER_SOURCE`] at runtime (no Xcode toolchain is needed at
//! build time), and builds the two compute pipelines. [`Backend::run`]
//! uploads a prepared [`Job`] into shared (unified-memory) buffers, encodes
//! the bucket-accumulation dispatch followed by one dispatch per reduction
//! level into a single command buffer, waits for completion, and reads the
//! per-window results back.
//!
//! Metal devices, command queues, and pipeline states are thread-safe, and
//! every buffer here is created per call, so a backend can serve MSMs from
//! several threads at once; the GPU serializes them.

mod objc;

use std::ffi::c_void;
use std::fmt;
use std::mem::size_of;

use self::objc::{
    AutoreleasePool, COMMAND_BUFFER_STATUS_COMPLETED, Id, MtlSize, Object, RESOURCE_OPTIONS_SHARED,
    sel,
};
use crate::curve::{Affine, Jacobian};
use crate::field::{Field, Limbs};
use crate::pipeline::{Backend, Error, Job};

/// Threads per threadgroup for the one-dimensional dispatches; capped by
/// the pipeline's `maxTotalThreadsPerThreadgroup`.
const THREADS_PER_THREADGROUP: usize = 64;

/// `FieldParams` in the shader.
#[repr(C)]
#[derive(Clone, Copy)]
struct FieldParams {
    modulus: Limbs,
    one: Limbs,
}

/// `AccumulateParams` in the shader.
#[repr(C)]
#[derive(Clone, Copy)]
struct AccumulateParams {
    total_buckets: u32,
}

/// `ReduceParams` in the shader.
#[repr(C)]
#[derive(Clone, Copy)]
struct ReduceParams {
    windows: u32,
    input_len: u32,
    chunks: u32,
    chunk_log2: u32,
    has_plain: u32,
}

/// A compiled compute pipeline and its threadgroup width.
struct Pipeline {
    state: Object,
    threads_per_threadgroup: usize,
}

/// An open Metal device with the MSM kernels compiled.
pub struct Metal {
    device: Object,
    queue: Object,
    accumulate: Pipeline,
    reduce: Pipeline,
    device_name: String,
}

// SAFETY: MTLDevice, MTLCommandQueue, and MTLComputePipelineState are
// documented as thread-safe, and `run` creates every other object per call
// inside its own autorelease pool.
unsafe impl Send for Metal {}
unsafe impl Sync for Metal {}

impl fmt::Debug for Metal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Metal")
            .field("device_name", &self.device_name)
            .finish_non_exhaustive()
    }
}

impl Metal {
    /// Opens the system default device and compiles the kernels.
    pub fn open() -> Result<Metal, Error> {
        let _pool = AutoreleasePool::push();
        let device = Object::owned(objc::create_system_default_device())
            .ok_or_else(|| Error("no Metal device available".into()))?;
        // SAFETY: `name` returns an autoreleased NSString.
        let device_name =
            objc::string_contents(unsafe { objc::send_id(device.id(), sel(c"name")) });

        // SAFETY: `newCommandQueue` returns an owned MTLCommandQueue or nil.
        let queue = Object::owned(unsafe { objc::send_id(device.id(), sel(c"newCommandQueue")) })
            .ok_or_else(|| Error("could not create a Metal command queue".into()))?;

        let source = std::ffi::CString::new(crate::SHADER_SOURCE)
            .map_err(|_| Error("shader source contains a NUL byte".into()))?;
        let source = objc::nsstring(&source);
        let mut error: Id = std::ptr::null_mut();
        // SAFETY: `newLibraryWithSource:options:error:` with nil options
        // returns an owned MTLLibrary, or nil with `error` set.
        let library = unsafe {
            objc::send_library(
                device.id(),
                sel(c"newLibraryWithSource:options:error:"),
                source,
                std::ptr::null_mut(),
                &mut error,
            )
        };
        let library = Object::owned(library).ok_or_else(|| {
            Error(format!(
                "Metal shader compilation failed: {}",
                objc::error_description(error)
            ))
        })?;

        let accumulate = Self::pipeline(&device, &library, c"accumulate_buckets")?;
        let reduce = Self::pipeline(&device, &library, c"reduce_level")?;

        Ok(Metal {
            device,
            queue,
            accumulate,
            reduce,
            device_name,
        })
    }

    /// The device's advertised name.
    pub fn device_name(&self) -> &str {
        &self.device_name
    }

    fn pipeline(
        device: &Object,
        library: &Object,
        name: &std::ffi::CStr,
    ) -> Result<Pipeline, Error> {
        // SAFETY: `newFunctionWithName:` returns an owned MTLFunction or nil.
        let function = unsafe {
            objc::send_id_id(
                library.id(),
                sel(c"newFunctionWithName:"),
                objc::nsstring(name),
            )
        };
        let function = Object::owned(function).ok_or_else(|| {
            Error(format!(
                "kernel {} missing from the compiled library",
                name.to_string_lossy()
            ))
        })?;
        let mut error: Id = std::ptr::null_mut();
        // SAFETY: `newComputePipelineStateWithFunction:error:` returns an
        // owned pipeline state or nil with `error` set.
        let state = unsafe {
            objc::send_pipeline(
                device.id(),
                sel(c"newComputePipelineStateWithFunction:error:"),
                function.id(),
                &mut error,
            )
        };
        let state = Object::owned(state).ok_or_else(|| {
            Error(format!(
                "pipeline {} failed: {}",
                name.to_string_lossy(),
                objc::error_description(error)
            ))
        })?;
        // SAFETY: `maxTotalThreadsPerThreadgroup` returns an NSUInteger.
        let max_threads =
            unsafe { objc::send_usize(state.id(), sel(c"maxTotalThreadsPerThreadgroup")) };
        Ok(Pipeline {
            state,
            threads_per_threadgroup: THREADS_PER_THREADGROUP.min(max_threads.max(1)),
        })
    }

    /// A shared buffer initialized from `items`.
    fn upload<T: Copy>(&self, items: &[T]) -> Result<Object, Error> {
        let length = std::mem::size_of_val(items);
        if length == 0 {
            return self.allocate(1);
        }
        // SAFETY: `newBufferWithBytes:length:options:` copies `length`
        // bytes from a valid pointer and returns an owned MTLBuffer.
        let buffer = unsafe {
            objc::send_buffer_bytes(
                self.device.id(),
                sel(c"newBufferWithBytes:length:options:"),
                items.as_ptr() as *const c_void,
                length,
                RESOURCE_OPTIONS_SHARED,
            )
        };
        Object::owned(buffer)
            .ok_or_else(|| Error(format!("could not allocate a {length}-byte buffer")))
    }

    /// An uninitialized shared buffer of `length` bytes.
    fn allocate(&self, length: usize) -> Result<Object, Error> {
        // SAFETY: `newBufferWithLength:options:` returns an owned MTLBuffer.
        let buffer = unsafe {
            objc::send_buffer_length(
                self.device.id(),
                sel(c"newBufferWithLength:options:"),
                length.max(1),
                RESOURCE_OPTIONS_SHARED,
            )
        };
        Object::owned(buffer)
            .ok_or_else(|| Error(format!("could not allocate a {length}-byte buffer")))
    }

    /// Encodes one dispatch of `pipeline` over `threads` threads with the
    /// given buffers bound at indices 0.., on a fresh encoder of `command_buffer`.
    fn dispatch(
        command_buffer: Id,
        pipeline: &Pipeline,
        buffers: &[Id],
        threads: usize,
    ) -> Result<(), Error> {
        // SAFETY: `computeCommandEncoder` returns an autoreleased encoder
        // (we are inside `run`'s pool); the remaining calls are the plain
        // encoder API with live objects.
        unsafe {
            let encoder = objc::send_id(command_buffer, sel(c"computeCommandEncoder"));
            if encoder.is_null() {
                return Err(Error("could not create a compute command encoder".into()));
            }
            objc::send_void_id(
                encoder,
                sel(c"setComputePipelineState:"),
                pipeline.state.id(),
            );
            for (index, &buffer) in buffers.iter().enumerate() {
                objc::send_set_buffer(encoder, sel(c"setBuffer:offset:atIndex:"), buffer, 0, index);
            }
            objc::send_dispatch(
                encoder,
                sel(c"dispatchThreads:threadsPerThreadgroup:"),
                MtlSize::linear(threads.max(1)),
                MtlSize::linear(pipeline.threads_per_threadgroup),
            );
            objc::send_void(encoder, sel(c"endEncoding"));
        }
        Ok(())
    }
}

impl Backend for Metal {
    fn run(&self, job: &Job, field: &Field) -> Result<Vec<Jacobian>, Error> {
        let _pool = AutoreleasePool::push();
        let plan = &job.plan;
        let windows = plan.windows as usize;
        let total_slots = plan.total_slots();

        let field_params = self.upload(&[FieldParams {
            modulus: field.modulus,
            one: field.one,
        }])?;
        let bases = self.upload::<Affine>(&job.bases)?;
        let terms = self.upload(&job.terms)?;
        let offsets = self.upload(&job.offsets)?;
        let buckets = self.allocate(total_slots * size_of::<Jacobian>())?;
        let accumulate_params = self.upload(&[AccumulateParams {
            // Bounded by the planner: at most 8 windows of 2^15 + 1 slots.
            total_buckets: total_slots as u32,
        }])?;

        // SAFETY: `commandBuffer` returns an autoreleased command buffer.
        let command_buffer = unsafe { objc::send_id(self.queue.id(), sel(c"commandBuffer")) };
        if command_buffer.is_null() {
            return Err(Error("could not create a command buffer".into()));
        }

        Self::dispatch(
            command_buffer,
            &self.accumulate,
            &[
                bases.id(),
                terms.id(),
                offsets.id(),
                buckets.id(),
                field_params.id(),
                accumulate_params.id(),
            ],
            total_slots,
        )?;

        // The reduction levels ping-pong between freshly allocated output
        // pairs; the buckets are level 0's weighted input.
        let mut weighted = buckets;
        let mut plain: Option<Object> = None;
        let mut level_params = Vec::with_capacity(plan.levels.len());
        for level in &plan.levels {
            let chunks = level.chunks as usize;
            let out_plain = self.allocate(windows * chunks * size_of::<Jacobian>())?;
            let out_weighted = self.allocate(windows * chunks * size_of::<Jacobian>())?;
            let params = self.upload(&[ReduceParams {
                windows: plan.windows,
                input_len: level.input_len,
                chunks: level.chunks,
                chunk_log2: plan.chunk_log2,
                has_plain: plain.is_some() as u32,
            }])?;
            let plain_in = plain.as_ref().map_or(weighted.id(), Object::id);
            Self::dispatch(
                command_buffer,
                &self.reduce,
                &[
                    weighted.id(),
                    plain_in,
                    out_plain.id(),
                    out_weighted.id(),
                    field_params.id(),
                    params.id(),
                ],
                windows * chunks,
            )?;
            // Keep every level's inputs alive until the GPU has run.
            level_params.push((weighted, plain, params));
            weighted = out_weighted;
            plain = Some(out_plain);
        }

        // SAFETY: commit and wait on the live command buffer; `status`
        // returns an NSUInteger; `error` an autoreleased NSError or nil.
        let status = unsafe {
            objc::send_void(command_buffer, sel(c"commit"));
            objc::send_void(command_buffer, sel(c"waitUntilCompleted"));
            objc::send_usize(command_buffer, sel(c"status"))
        };
        if status != COMMAND_BUFFER_STATUS_COMPLETED {
            // SAFETY: as above.
            let error = unsafe { objc::send_id(command_buffer, sel(c"error")) };
            return Err(Error(format!(
                "Metal command buffer finished with status {status}: {}",
                objc::error_description(error)
            )));
        }

        let results = plain.as_ref().unwrap_or(&weighted);
        // SAFETY: `contents` of a shared buffer is CPU-visible memory of the
        // requested length, written by the completed command buffer;
        // `Jacobian` is a plain `repr(C)` array of `u32`s, so every bit
        // pattern is a valid value.
        let output = unsafe {
            let pointer = objc::send_id(results.id(), sel(c"contents")) as *const Jacobian;
            if pointer.is_null() {
                return Err(Error("result buffer has no CPU-visible contents".into()));
            }
            std::slice::from_raw_parts(pointer, windows).to_vec()
        };
        drop(level_params);
        Ok(output)
    }
}
