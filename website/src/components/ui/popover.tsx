"use client"

import type {
  DialogTriggerProps,
  PopoverProps as PopoverPrimitiveProps,
} from "react-aria-components"

import { composeTailwindRenderProps } from "@/lib/primitive"
import {
  DialogTrigger as DialogTriggerPrimitive,
  OverlayArrow,
  Popover as PopoverPrimitive,
} from "react-aria-components"

import {
  DialogBody,
  DialogClose,
  DialogDescription,
  DialogFooter,
  DialogHeader,
  DialogTitle,
  DialogTrigger,
} from "./dialog"

type PopoverProps = DialogTriggerProps
const Popover = (props: PopoverProps) => {
  return <DialogTriggerPrimitive {...props} />
}

const PopoverTitle = DialogTitle
const PopoverHeader = DialogHeader
const PopoverBody = DialogBody
const PopoverFooter = DialogFooter

type PopoverContentProps = PopoverPrimitiveProps & {
  ref?: React.Ref<HTMLDivElement>
  showArrow?: boolean
}

const PopoverContent = ({
  children,
  className,
  ref,
  showArrow = false,
  ...props
}: PopoverContentProps) => {
  const offset = props.offset ?? (showArrow ? 12 : 8)
  return (
    <PopoverPrimitive
      className={composeTailwindRenderProps(className, [
        "group/popover bg-overlay text-overlay-fg max-w-xs min-w-(--trigger-width) rounded-xl border shadow-xs outline-hidden transition-transform [--gutter:--spacing(6)] sm:text-sm dark:backdrop-saturate-200 **:[[role=dialog]]:[--gutter:--spacing(4)]",
        "entering:fade-in entering:animate-in",
        "exiting:fade-out exiting:animate-out",
        "placement-left:entering:slide-in-from-right-1 placement-right:entering:slide-in-from-left-1 placement-top:entering:slide-in-from-bottom-1 placement-bottom:entering:slide-in-from-top-1",
        "placement-left:exiting:slide-out-to-right-1 placement-right:exiting:slide-out-to-left-1 placement-top:exiting:slide-out-to-bottom-1 placement-bottom:exiting:slide-out-to-top-1",
        "forced-colors:bg-[Canvas]",
      ])}
      offset={offset}
      ref={ref}
      {...props}
    >
      {(values) => (
        <>
          {showArrow && (
            <OverlayArrow className="group">
              <svg
                className="group-placement-left:-rotate-90 fill-overlay stroke-border group-placement-bottom:rotate-180 group-placement-right:rotate-90 block forced-colors:fill-[Canvas] forced-colors:stroke-[ButtonBorder]"
                height={12}
                viewBox="0 0 12 12"
                width={12}
              >
                <path d="M0 0 L6 6 L12 0" />
              </svg>
            </OverlayArrow>
          )}
          {typeof children === "function" ? children(values) : children}
        </>
      )}
    </PopoverPrimitive>
  )
}

const PopoverTrigger = DialogTrigger
const PopoverClose = DialogClose
const PopoverDescription = DialogDescription

Popover.Trigger = PopoverTrigger
Popover.Close = PopoverClose
Popover.Description = PopoverDescription
Popover.Content = PopoverContent
Popover.Body = PopoverBody
Popover.Footer = PopoverFooter
Popover.Header = PopoverHeader
Popover.Title = PopoverTitle

export type { PopoverContentProps, PopoverProps }
export { Popover, PopoverContent }
