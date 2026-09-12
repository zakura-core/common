use std::ffi::{CStr, CString};

fn main() {
    let hardware = CString::new(std::env::consts::ARCH).unwrap();
    let model = CString::new("local verification host").unwrap();
    let soc = CString::new("host CPU").unwrap();
    let os = CString::new(std::env::consts::OS).unwrap();
    let thermal = CString::new("unavailable").unwrap();
    let processors = std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1);

    // SAFETY: The inputs are live C strings, and the returned allocation is
    // released exactly once after copying it into a Rust string.
    unsafe {
        let result = orchard_ios_benchmark::orchard_ios_benchmark_run(
            hardware.as_ptr(),
            model.as_ptr(),
            soc.as_ptr(),
            os.as_ptr(),
            thermal.as_ptr(),
            processors,
        );
        assert!(!result.is_null());
        println!("{}", CStr::from_ptr(result).to_string_lossy());
        orchard_ios_benchmark::orchard_ios_benchmark_string_free(result);
    }
}
