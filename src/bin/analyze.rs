const USAGE: &str = "Usage: cargo run <filename>";

fn main() {
    // Parse command line arguments
    let mut args = std::env::args().skip(1);
    let input_file = args.next().expect(USAGE);

    todo!("analyze {}", input_file);
}
