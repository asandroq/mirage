
mod lang;
mod nonemptyvec;
mod sharedlist;

use std::{env, fmt, fs};


#[derive(Debug)]
enum ErrorKind {
    Io(std::io::Error),
    Lang(lang::Error),
    BadArgs,
}

#[derive(Debug)]
struct Error {
    kind: ErrorKind,
    msg: String,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.msg)
    }
}

impl From<std::io::Error> for Error {
    fn from(io_err: std::io::Error) -> Error {
	let msg = format!("io error: {}", io_err);
	Error {
	    kind: ErrorKind::Io(io_err),
	    msg,
	}
    }
}

impl From<lang::Error> for Error {
    fn from(lang_err: lang::Error) -> Error {
	let msg = format!("{}", lang_err);
	Error {
	    kind: ErrorKind::Lang(lang_err),
	    msg,
	}
    }
}

type Result<T> = std::result::Result<T, Error>;

fn run() -> Result<()> {
    let arg = env::args().nth(1).ok_or(
	Error {
	    kind: ErrorKind::BadArgs,
	    msg: format!("Filename argument is missing"),
	}
    )?;
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
