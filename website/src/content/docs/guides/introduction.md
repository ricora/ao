---
title: Introduction
description: A statically typed language powered by WebAssembly
---

Ao is a statically typed language powered by WebAssembly.

## Features

- **Statically Typed**: Ao is a statically typed language. In the future, it will include a type inference system.
- **WebAssembly**: Ao emits Wasm components, not native binaries. For more information, see the [Component Model design and specification](https://github.com/WebAssembly/component-model).
  - **Write Once, Run Anywhere**: Ao can run on any platform that supports WebAssembly. Write your code once and run it in the browser, on a server, or even on IoT devices.
- **Rust-Like Syntax**: Ao features a syntax similar to Rust. If you're familiar with Rust, learning Ao will be straightforward. You can think of Ao as Rust with garbage collection, or Go with Rust's syntax.
- **Garbage Collection**: Ao has a garbage collector, so you don't need to manually manage memory. For more information, see the [GC Proposal for WebAssembly](https://github.com/WebAssembly/gc).

## Getting Started

To get started with Ao, try the [online playground](/playground/). You can write code in the left editor and see the output, ast, and tokens in the right panel.

:::note
The playground is working without a backend server. The given code is compiled and executed entirely in the browser!
:::

For example, try writing the following code in the editor:

```ao
fn main() -> i32 {
    let a = 10;
    let b = 20;
    print_int(a + b);
    0
}
```

You should see the output `30` in the right panel.
