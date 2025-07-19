#[allow(warnings)]
mod bindings;

use anyhow::Context;
use bindings::Guest;
use code_generator::CodeGenerator;
use parser::parse;

#[derive(Debug, thiserror::Error)]
enum Error {
    #[error(transparent)]
    CodeGenerator(#[from] code_generator::Error),
}

impl std::convert::From<anyhow::Error> for bindings::Error {
    fn from(error: anyhow::Error) -> Self {
        bindings::Error {
            error: error.to_string(),
        }
    }
}

struct Component;

impl Guest for Component {
    fn compile(source: String) -> Result<bindings::Output, bindings::Error> {
        let ast = parse(&source).unwrap();
        let mut generator =
            CodeGenerator::new(ast.clone()).with_context(|| "Failed to create code generator")?;
        let mut wat = generator
            .generate()
            .with_context(|| "Failed to generate WAT")?;
        let wasm = wat.encode().with_context(|| "Failed to encode WAT")?;
        Ok(bindings::Output {
            ast: serde_json::to_string(&ast).with_context(|| "Failed to serialize AST")?,
            wasm,
        })
    }
}

bindings::export!(Component with_types_in bindings);
