#![deny(clippy::pedantic)]
#![allow(clippy::similar_names)]

mod collections;
mod error;
mod lang;

use crate::{error::Result, lang::interp::Interpreter};
use rustyline::{error::ReadlineError, Editor};
use std::{
    env,
    path::{Path, PathBuf},
};

fn main() -> Result<()> {
    let mut interp = Interpreter::new();
    interp.load_prelude()?;

    let mut rl = Editor::<()>::new()?;
    let hist_path = if let Ok(home) = env::var("HOME") {
        Path::new(&home).join(".mirage_history.txt")
    } else {
        PathBuf::from("mirage_history.txt")
    };
    if rl.load_history(&hist_path).is_err() {
        println!("No previous history.");
    }

    loop {
        let readline = rl.readline("λ> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                let res = interp.eval(&line, "REPL".to_string());
                match res {
                    Ok((val, ttype)) => println!("{val} : {ttype}"),
                    Err(err) => println!("Error: {err}"),
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            }
            Err(err) => {
                println!("Error: {err:?}");
                break;
            }
        }
    }

    rl.save_history(&hist_path)?;
    Ok(())
}
