use clap::Parser;
use code_generator::CodeGenerator;
use parser::parse;
use type_checker::TypeChecker;

#[derive(clap::Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(short, long, default_value_t = Mode::Compile)]
    mode: Mode,

    #[arg(short, long, default_value_t = false)]
    command: bool,

    source: String,

    #[arg(short, long)]
    output: Option<String>,
}

#[derive(Clone)]
enum Mode {
    Parse,
    Compile,
}

impl std::str::FromStr for Mode {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "parse" => Ok(Self::Parse),
            "compile" => Ok(Self::Compile),
            _ => Err("Invalid mode".to_string()),
        }
    }
}

impl std::fmt::Display for Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Parse => write!(f, "parse"),
            Self::Compile => write!(f, "compile"),
        }
    }
}

fn main() {
    let args = Args::parse();

    let source_id = if args.command {
        "command".to_string()
    } else {
        args.source.clone()
    };
    let source = if args.command {
        args.source
    } else {
        std::fs::read_to_string(&args.source).expect("Failed to read source file")
    };
    match args.mode {
        Mode::Parse => {
            let ast = parse(&source).unwrap(); // TODO: handle errors properly
            if let Some(output) = args.output {
                std::fs::write(output, format!("{ast:#?}")).expect("Failed to write output");
            } else {
                println!("{ast:#?}");
            }
        }
        Mode::Compile => {
            let ast = parse(&source).unwrap(); // TODO: handle errors properly

            let mut typechecker = TypeChecker::new();
            let typecheck_result = typechecker.check_program(&ast);
            if let Err(e) = typecheck_result {
                let error_msg = typechecker.format_error(&e, &source_id, &source);
                eprintln!("{error_msg}");
                return;
            }

            let mut generator = CodeGenerator::new(ast).unwrap();
            let mut wat = generator.generate().unwrap();
            let wasm = wat.encode().unwrap();
            if let Some(output) = args.output {
                std::fs::write(output, &wasm).expect("Failed to write output");
            } else {
                println!("{wat:#?}");
            }
        }
    }
}
