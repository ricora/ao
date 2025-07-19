import type React from "react"
import type {
  ComboBoxProps as ComboboxPrimitiveProps,
  InputProps,
  ListBoxProps,
  PopoverProps,
} from "react-aria-components"

import { composeTailwindRenderProps } from "@/lib/primitive"
import { IconChevronsY } from "@intentui/icons"
import {
  ComboBoxContext,
  ComboBox as ComboboxPrimitive,
  ListBox,
  useSlottedContext,
} from "react-aria-components"

import { Button } from "./button"
import {
  DropdownDescription,
  DropdownItem,
  DropdownLabel,
  DropdownSection,
} from "./dropdown"
import {
  Description,
  FieldError,
  FieldGroup,
  type FieldProps,
  Input,
  Label,
} from "./field"
import { PopoverContent } from "./popover"

type ComboBoxProps<T extends object> = FieldProps &
  Omit<ComboboxPrimitiveProps<T>, "children"> & {
    children: React.ReactNode
  }

const ComboBox = <T extends object>({
  children,
  className,
  description,
  errorMessage,
  label,
  ...props
}: ComboBoxProps<T>) => {
  return (
    <ComboboxPrimitive
      data-slot="combo-box"
      {...props}
      className={composeTailwindRenderProps(
        className,
        "group flex w-full flex-col gap-y-1",
      )}
    >
      {label && <Label>{label}</Label>}
      {children}
      {description && <Description>{description}</Description>}
      <FieldError>{errorMessage}</FieldError>
    </ComboboxPrimitive>
  )
}

type ComboBoxListProps<T extends object> = Omit<
  ListBoxProps<T>,
  "layout" | "orientation"
> &
  Pick<PopoverProps, "placement"> & {
    popover?: Omit<PopoverProps, "children">
  }

const ComboBoxList = <T extends object>({
  children,
  className,
  items,
  popover,
  ...props
}: ComboBoxListProps<T>) => {
  return (
    <PopoverContent
      className={composeTailwindRenderProps(
        popover?.className,
        "min-w-(--trigger-width) scroll-py-1 overflow-y-auto overscroll-contain",
      )}
      {...popover}
    >
      <ListBox
        className={composeTailwindRenderProps(
          className,
          "grid max-h-96 w-full grid-cols-[auto_1fr] flex-col gap-y-1 p-1 outline-hidden *:[[role='group']+[role=group]]:mt-4 *:[[role='group']+[role=separator]]:mt-1",
        )}
        items={items}
        layout="stack"
        orientation="vertical"
        {...props}
      >
        {children}
      </ListBox>
    </PopoverContent>
  )
}

const ComboBoxInput = (props: InputProps) => {
  const context = useSlottedContext(ComboBoxContext)
  return (
    <FieldGroup>
      <Input {...props} placeholder={props?.placeholder} />
      <Button
        className="pressed:bg-transparent **:data-[slot=icon]:pressed:text-fg **:data-[slot=icon]:text-muted-fg **:data-[slot=icon]:hover:text-fg rounded outline-offset-0 hover:bg-transparent active:bg-transparent forced-colors:group-disabled:border-[GrayText] forced-colors:group-disabled:text-[GrayText]"
        intent="plain"
        size="sq-xs"
      >
        {!context?.inputValue && (
          <IconChevronsY
            className="text-muted-fg group-open:text-fg size-4 shrink-0"
            data-slot="chevron"
          />
        )}
      </Button>
    </FieldGroup>
  )
}

const ComboBoxSection = DropdownSection
const ComboBoxOption = DropdownItem
const ComboBoxLabel = DropdownLabel
const ComboBoxDescription = DropdownDescription

ComboBox.Input = ComboBoxInput
ComboBox.List = ComboBoxList
ComboBox.Option = ComboBoxOption
ComboBox.Label = ComboBoxLabel
ComboBox.Description = ComboBoxDescription
ComboBox.Section = ComboBoxSection

export type { ComboBoxListProps, ComboBoxProps }
export { ComboBox }
