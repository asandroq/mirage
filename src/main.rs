#![allow(clippy::similar_names)]

mod collections;
mod error;
mod lang;

use crate::{error::Result, lang::interp::Interpreter};
use rustyline::{error::ReadlineError, Editor};

fn main() -> Result<()> {
    let mut interp = Interpreter::new();
    interp.load_prelude()?;

    let mut rl = Editor::<()>::new();
    if rl.load_history("history.txt").is_err() {
        println!("No previous history.");
    }
    loop {
        let readline = rl.readline("λ> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                let res = interp.eval(&line, "stdin".to_string());
                match res {
                    Ok(val) => println!("{val}"),
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
                println!("Error: {:?}", err);
                break;
            }
        }
    }
    rl.save_history("history.txt")?;

    Ok(())
}
