mod fmt;

fn main() {
    let mut in_text = String::new();
    let json: serde_json::Value = serde_json::from_reader(std::io::stdin()).unwrap();

    let mut fmt = fmt::Formatter::new(std::io::stdout());
    fmt.fmt(&json).unwrap();
}
