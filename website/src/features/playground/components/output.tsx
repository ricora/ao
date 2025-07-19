import { Tab, TabList, TabPanel, Tabs } from "@/components/ui/tabs"
import MonacoEditor from "@monaco-editor/react"
import { type FC, memo } from "react"

import { type Output as OutputType } from "../hooks/use-playground"

type EditorProps = {
  language: string
  value: string
}

const Editor: FC<EditorProps> = memo(({ language, value }) => {
  return (
    <MonacoEditor
      height="100%"
      language={language}
      onMount={(editor) => {
        editor.updateOptions({
          minimap: { enabled: false },
          readOnly: true,
          theme: "vs-dark",
        })
      }}
      value={value}
    />
  )
})
Editor.displayName = "Editor"

export type OutputProps = {
  output: OutputType | undefined
}

export const Output: FC<OutputProps> = memo(({ output }) => {
  return (
    <Tabs className="h-full flex-1 gap-0 border-x-0">
      <TabList className="px-4 pt-2">
        <Tab id="output">Output</Tab>
        <Tab id="ast">AST</Tab>
      </TabList>
      <TabPanel className="h-full" id="output">
        <Editor language="plaintext" value={output?.output ?? ""} />
      </TabPanel>
      <TabPanel className="h-full" id="ast">
        <Editor language="json" value={JSON.stringify(output?.ast, null, 2)} />
      </TabPanel>
    </Tabs>
  )
})
Output.displayName = "Output"
