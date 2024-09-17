include!("src/common.rs");

fn main() {
    let filename = most_recent_onnx_model().unwrap();
    println!("cargo:warning=Compiling model: {}", filename.display());
}
