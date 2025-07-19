"use client"

import { composeRenderProps } from "react-aria-components"
import { type ClassNameValue, twMerge } from "tailwind-merge"

function composeTailwindRenderProps<T>(
  className: ((v: T) => string) | string | undefined,
  tailwind: ClassNameValue,
): ((v: T) => string) | string {
  return composeRenderProps(className, (className) =>
    twMerge(tailwind, className),
  )
}

export { composeTailwindRenderProps }
