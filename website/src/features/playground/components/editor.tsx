import { Button } from "@/components/ui/button"
import MonacoEditor from "@monaco-editor/react"
import { type FC, memo } from "react"
import { twMerge } from "tailwind-merge"

export type EditorProps = {
  className?: string
  code: string
  run: () => void
  setCode: (code: string) => void
}

export const Editor: FC<EditorProps> = memo(
  ({ className, code, run, setCode }) => {
    return (
      <div className={twMerge("relative h-full flex-1", className)}>
        <MonacoEditor
          height="100%"
          language="plaintext"
          onChange={(value) => setCode(value ?? "")}
          onMount={(editor) => {
            editor.updateOptions({
              minimap: { enabled: false },
              theme: "vs-dark",
            })
          }}
          value={code}
        />
        <Button
          className="absolute right-4 bottom-4 font-bold transition"
          onPress={run}
        >
          Run
        </Button>
      </div>
    )
  },
)
Editor.displayName = "Editor"
