
mod lang;
mod nonemptyvec;
mod sharedlist;

use std::{env, fs};
use thiserror::Error;

#[derive(Debug, Error)]
enum Error {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("Language error: {0}")]    
    Lang(#[from] lang::Error),

    #[error("Bad arguments")]
    BadArgs,
}

type Result<T> = std::result::Result<T, Error>;

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
