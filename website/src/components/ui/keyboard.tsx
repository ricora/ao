"use client"

import { Keyboard as KeyboardPrimitive } from "react-aria-components"
import { twMerge } from "tailwind-merge"

type KeyboardProps = React.HTMLAttributes<HTMLElement> & {
  classNames?: {
    base?: string
    kbd?: string
  }
  keys: string | string[]
}

const Keyboard = ({ className, classNames, keys, ...props }: KeyboardProps) => {
  return (
    <KeyboardPrimitive
      className={twMerge(
        "hidden font-mono text-current/60 group-hover:text-fg group-focus:text-fg group-focus:opacity-90 group-disabled:opacity-50 lg:inline-flex forced-colors:group-focus:text-[HighlightText] forced-colors:group-focus:text-[HighlightText]",
        classNames?.base,
      )}
      {...props}
    >
      {(Array.isArray(keys) ? keys : [...keys]).map((char, index) => (
        <kbd
          className={twMerge(
            "tracking-widest",
            index > 0 && char.length > 1 && "pl-1",
            classNames?.kbd,
          )}
          key={index}
        >
          {char}
        </kbd>
      ))}
    </KeyboardPrimitive>
  )
}

export type { KeyboardProps }
export { Keyboard }
