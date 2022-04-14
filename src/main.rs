mod error;
mod lang;
mod nonemptyvec;
mod sharedlist;

use crate::error::{Error, Result};
use std::{env, fs};

fn run() -> Result<()> {
    let arg = env::args().nth(1).ok_or(Error::BadArgs)?;
    let input = fs::read_to_string(&arg)?;
    let val = lang::eval_str(&input, arg)?;
    println!("> {}", val);

    Ok(())
}

fn main() {
    std::process::exit(
        match run() {
            Ok(_) => 0,
            Err(err) => {
                eprintln!("Error: {}", err);
                1
            }
        }
    )
}
