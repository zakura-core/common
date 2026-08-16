use std::path::PathBuf;

fn main() {
    let mut build = cc::Build::new();
    let mut any = false;
    for entry in std::fs::read_dir("src").unwrap() {
        let path: PathBuf = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) == Some("S") {
            println!("cargo:rerun-if-changed={}", path.display());
            build.file(&path);
            any = true;
        }
    }
    if any {
        build.compile("field_backend_proto");
    }
}
