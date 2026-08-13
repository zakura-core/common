use core::{ffi::c_void, mem::MaybeUninit};

use pasta_curves::{pallas, vesta};

const STATUS_OK: i32 = 0;
const STATUS_INVALID_ARGUMENT: i32 = 1;
const STATUS_ALLOCATION_FAILURE: i32 = 2;
const STATUS_NATIVE_FAILURE: i32 = 3;

const _: () = {
    const FIELD_BYTES: usize = 4 * size_of::<u64>();
    const FIELD_ALIGNMENT: usize = align_of::<u64>();

    assert!(size_of::<pallas::Base>() == FIELD_BYTES);
    assert!(align_of::<pallas::Base>() == FIELD_ALIGNMENT);
    assert!(size_of::<pallas::Scalar>() == FIELD_BYTES);
    assert!(align_of::<pallas::Scalar>() == FIELD_ALIGNMENT);
    assert!(size_of::<pallas::Affine>() == 2 * FIELD_BYTES);
    assert!(align_of::<pallas::Affine>() == FIELD_ALIGNMENT);
    assert!(size_of::<pallas::Point>() == 3 * FIELD_BYTES);
    assert!(align_of::<pallas::Point>() == FIELD_ALIGNMENT);

    assert!(size_of::<vesta::Base>() == FIELD_BYTES);
    assert!(align_of::<vesta::Base>() == FIELD_ALIGNMENT);
    assert!(size_of::<vesta::Scalar>() == FIELD_BYTES);
    assert!(align_of::<vesta::Scalar>() == FIELD_ALIGNMENT);
    assert!(size_of::<vesta::Affine>() == 2 * FIELD_BYTES);
    assert!(align_of::<vesta::Affine>() == FIELD_ALIGNMENT);
    assert!(size_of::<vesta::Point>() == 3 * FIELD_BYTES);
    assert!(align_of::<vesta::Point>() == FIELD_ALIGNMENT);
};

unsafe extern "C" {
    fn zakura_pasta_msm_pallas_vartime(
        output: *mut c_void,
        points: *const c_void,
        scalars: *const c_void,
        len: usize,
    ) -> i32;

    fn zakura_pasta_msm_vesta_vartime(
        output: *mut c_void,
        points: *const c_void,
        scalars: *const c_void,
        len: usize,
    ) -> i32;
}

pub(super) unsafe fn pallas_vartime(
    points: &[pallas::Affine],
    scalars: &[pallas::Scalar],
) -> pallas::Point {
    let mut output = MaybeUninit::<pallas::Point>::uninit();
    // SAFETY: The caller establishes the slice and layout invariants. The
    // output is only read after the native function reports success.
    let status = unsafe {
        zakura_pasta_msm_pallas_vartime(
            output.as_mut_ptr().cast(),
            points.as_ptr().cast(),
            scalars.as_ptr().cast(),
            points.len(),
        )
    };
    check_status(status);
    // SAFETY: A successful native call initializes every output limb.
    unsafe { output.assume_init() }
}

pub(super) unsafe fn vesta_vartime(
    points: &[vesta::Affine],
    scalars: &[vesta::Scalar],
) -> vesta::Point {
    let mut output = MaybeUninit::<vesta::Point>::uninit();
    // SAFETY: The caller establishes the slice and layout invariants. The
    // output is only read after the native function reports success.
    let status = unsafe {
        zakura_pasta_msm_vesta_vartime(
            output.as_mut_ptr().cast(),
            points.as_ptr().cast(),
            scalars.as_ptr().cast(),
            points.len(),
        )
    };
    check_status(status);
    // SAFETY: A successful native call initializes every output limb.
    unsafe { output.assume_init() }
}

fn check_status(status: i32) {
    match status {
        STATUS_OK => {}
        STATUS_INVALID_ARGUMENT => panic!("native pasta-msm rejected its arguments"),
        STATUS_ALLOCATION_FAILURE => panic!("native pasta-msm allocation failed"),
        STATUS_NATIVE_FAILURE => panic!("native pasta-msm failed"),
        _ => panic!("native pasta-msm returned an unknown status: {status}"),
    }
}
