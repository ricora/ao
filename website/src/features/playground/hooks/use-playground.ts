import { useState } from "react"

import { compile } from "../../../../generated/tools/tools"
import { runCli, transpile } from "../lib/wasm"

export type Output = {
  ast: unknown
  output: string
}

type WasiCliRun = {
  "wasi:cli/run@0.2.2": {
    run: () => void
  }
}

export const usePlayground = () => {
  const [code, setCode] = useState("fn main () -> i32 { 0 }")
  const [output, setOutput] = useState<Output | undefined>()

  const run = async () => {
    const { ast, wasm } = compile(code)
    const { "wasi:cli/run@0.2.2": entrypoint } = await transpile<WasiCliRun>(
      wasm,
      "main",
    )
    const output = runCli(entrypoint.run)
    setOutput({
      ast: JSON.parse(ast),
      output,
    })
  }

  return { code, output, run, setCode }
}
