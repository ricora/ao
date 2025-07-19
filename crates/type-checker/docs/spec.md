# Ao Type Checker Specification

## Types

- `i32`: 32-bit signed integer
- `i64`: 64-bit signed integer

## Type Checking Rules

### Functions

- Function body's last expression type must match declared return type
- Empty blocks have type `()`

### Variables

- `let x: T = expr` - `expr` must have type `T`, immutable
- `var x: T = expr` - `expr` must have type `T`, mutable
- `var x: T` - uninitialized, must assign before use

### Expressions

#### Binary Operations

- `+`, `-`, `*`, `/`: operands same numeric type → same type
- `<`, `<=`, `>`, `>=`, `==`, `!=`: operands same type → `bool`
- `&&`, `||`: operands `bool` → `bool`

#### Unary Operations

- `-expr`: `expr` numeric type → same type
- `!expr`: `expr` bool type → `bool`

#### Assignment

- `x = expr`: `x` mutable, `expr` type matches `x` type

#### Function Calls

- Argument count and types must match parameters
- Result type is function's return type

#### Identifiers

- Must be declared and initialized

#### Literals

- Integer literals default to `i32`

### Control Flow

- `if` condition must be `bool`
- `if` blocks have type `()`

### Blocks

- `{statements expr}` → type of `expr`
- `{statements}` → `()`

## Errors

1. Type mismatch
2. Undefined identifier
3. Uninitialized variable use
4. Assignment to immutable variable
5. Function call argument mismatch
6. Duplicate definition

## Type Environment

```rust
struct TypeEnvironment {
    variables: HashMap<String, (Type, bool, bool)>, // (type, mutable, initialized)
    functions: HashMap<String, (Vec<Type>, Type)>,  // (params, return)
}
```
