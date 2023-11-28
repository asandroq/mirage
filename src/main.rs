#![allow(clippy::similar_names)]

mod collections;
mod error;
mod lang;

use crate::{error::Result, lang::interp::Interpreter};
use rustyline::{error::ReadlineError, DefaultEditor};
use std::{
    env,
    path::{Path, PathBuf},
};

/// A Read-Eval-Print loop.
fn repl(mut interp: Interpreter) -> Result<()> {
    let mut rl = DefaultEditor::new()?;
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
                rl.add_history_entry(line.as_str())?;
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

fn main() -> Result<()> {
    // Create a new interpreter with a preloaded prelude.
    let mut interp = Interpreter::new();
    interp.load_prelude()?;

    // If given an argument, load the file as a module before entering the REPL.
    let mut args = env::args();
    args.next();
    if let Some(input) = args.next() {
        interp.load_file(&input)?;
    }

    repl(interp)
}
