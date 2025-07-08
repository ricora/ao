# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is the **Ao** programming language - a language that compiles to WebAssembly components. The project consists of:

- **Language compiler** (`src/main.rs`) - A CLI tool that can parse source code and compile it to WASM
- **AST definitions** (`crates/ast/`) - Abstract syntax tree structures for the language
- **Parser** (`crates/parser/`) - Chumsky-based parser using Logos lexer
- **Code generator** (`crates/code-generator/`) - Generates WebAssembly Text format from AST
- **Website** (`website/`) - Astro-based documentation and playground

## Common Commands

### Rust Development Commands (via cargo-make)

```bash
# Build the project
cargo make build

# Run tests
cargo make test

# Run tests with coverage
cargo make test-coverage

# Format code (check only)
cargo make format

# Format code (auto-fix)
cargo make format-write

# Lint code (check only)
cargo make lint

# Lint code (auto-fix)
cargo make lint-write

# Check for unused dependencies
cargo make machete
```

### Language Usage

```bash
# Compile source code to WASM
cargo run -- source.ao -o output.wasm

# Parse only (output AST)
cargo run -- --mode parse source.ao

# Compile from command line string
cargo run -- --command "fn main() -> i32 { 42 }"
```

## Architecture

### Parser Architecture

- **Lexer**: Uses Logos for tokenization (`crates/parser/src/token.rs`)
- **Parser**: Uses Chumsky for parsing with error recovery
- **AST**: Strongly typed AST with location information for all nodes

### Code Generation

- Generates WebAssembly Text format (.wat) using `wast` crate
- Uses a template (`crates/code-generator/src/template.wat`) for the component structure
- Translates AST nodes to WASM instructions
- Supports WASI for I/O operations (print_int, print_char functions)

### Testing

- **Parser tests**: Uses `insta` for snapshot testing
- **Code generator tests**: Compiles and runs generated WASM using `wasmtime`
- **Integration tests**: End-to-end tests from source code to execution

## Development Workflow

1. **Parser changes**: Update `crates/parser/src/lib.rs` and run `cargo make test` to check snapshots
2. **Code generation**: Update `crates/code-generator/src/lib.rs` and test with integration tests
3. **Website changes**: Work in `website/` directory using pnpm commands

## Key Files

- `src/main.rs` - CLI entry point
- `crates/ast/src/lib.rs` - AST node definitions
- `crates/parser/src/lib.rs` - Main parser implementation
- `crates/code-generator/src/lib.rs` - WASM code generation
- `crates/code-generator/src/template.wat` - WASM component template
- `website/src/features/playground/` - Web-based language playground
