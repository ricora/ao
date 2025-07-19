import type { FC } from "react"

import { usePlayground } from "../hooks/use-playground"
import { Editor } from "./editor"
import { Output } from "./output"

export const Playground: FC = () => {
  const { code, output, run, setCode } = usePlayground()
  return (
    <div className="dark bg-bg text-fg flex h-full flex-row divide-x">
      <Editor code={code} run={run} setCode={setCode} />
      <Output output={output} />
    </div>
  )
}
