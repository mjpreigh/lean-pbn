use std::env;

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();

    let mut start_new = true;
    let mut out_str = "".to_string();
    let mut rules: Vec<String> = vec![];
    for arg in args {
        println!("arg : {}", arg);
        if arg.eq("") {
            start_new = true;
            rules.push(out_str.clone());
        } else if start_new {
            start_new = false;
            out_str = format!("Rule {} with premises", arg);
        } else {
            out_str = format!("{} {}", out_str, arg);
        }
    }
    rules.push(out_str.clone());

    print!("{}", rules.join("\n"))
}