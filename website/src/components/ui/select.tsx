import type {
  ListBoxProps,
  PopoverProps,
  SelectProps as SelectPrimitiveProps,
} from "react-aria-components"

import { composeTailwindRenderProps } from "@/lib/primitive"
import { IconChevronsY } from "@intentui/icons"
import {
  Button,
  ListBox,
  Select as SelectPrimitive,
  SelectValue,
} from "react-aria-components"
import { twJoin } from "tailwind-merge"

import type { FieldProps } from "./field"

import {
  DropdownDescription,
  DropdownItem,
  DropdownLabel,
  DropdownSection,
  DropdownSeparator,
} from "./dropdown"
import { Description, FieldError, Label } from "./field"
import { PopoverContent } from "./popover"

type SelectProps<T extends object> = FieldProps &
  SelectPrimitiveProps<T> & {
    items?: Iterable<T>
  }

const Select = <T extends object>({
  children,
  className,
  description,
  errorMessage,
  label,
  ...props
}: SelectProps<T>) => {
  return (
    <SelectPrimitive
      data-slot="select"
      {...props}
      className={composeTailwindRenderProps(
        className,
        "group/select flex w-full flex-col gap-y-1",
      )}
    >
      {(values) => (
        <>
          {label && <Label>{label}</Label>}
          {typeof children === "function" ? children(values) : children}
          {description && <Description>{description}</Description>}
          <FieldError>{errorMessage}</FieldError>
        </>
      )}
    </SelectPrimitive>
  )
}

type SelectListProps<T extends object> = Omit<
  ListBoxProps<T>,
  "layout" | "orientation"
> & {
  items?: Iterable<T>
  popover?: Omit<PopoverProps, "children">
}

const SelectList = <T extends object>({
  className,
  items,
  popover,
  ...props
}: SelectListProps<T>) => {
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
      />
    </PopoverContent>
  )
}

type SelectTriggerProps = React.ComponentProps<typeof Button> & {
  className?: string
  prefix?: React.ReactNode
}

const SelectTrigger = ({
  children,
  className,
  ...props
}: SelectTriggerProps) => {
  return (
    <Button
      className={composeTailwindRenderProps(
        className,
        twJoin([
          "inset-ring-input text-fg flex w-full min-w-0 cursor-default items-center gap-x-2 rounded-lg px-3.5 py-2 text-start shadow-[inset_0_1px_0_0_rgba(255,255,255,0.1)] inset-ring outline-hidden transition duration-200 sm:py-1.5 sm:pr-2 sm:pl-3 sm:text-sm/6 sm:*:text-sm/6 dark:shadow-none",
          "group-open/select:inset-ring-ring/70 group-open/select:ring-ring/20 group-open/select:ring-3",
          "forced-colors:group-disabled/select/select:text-[GrayText] group-disabled/select:opacity-50 forced-colors:group-disabled/select:inset-ring-[GrayText]",
          "focus:inset-ring-ring/70 focus:ring-ring/20 focus:ring-3",
          "hover:inset-ring-[color-mix(in_oklab,var(--color-input)_50%,var(--color-muted-fg)_25%)]",
          "group-open/select:invalid:inset-ring-danger/70 group-open/select:invalid:ring-danger/20 group-invalid/select:inset-ring-danger/70 group-invalid/select:ring-danger/20 group-focus/select:group-invalid/select:inset-ring-danger/70 group-focus/select:group-invalid/select:ring-danger/20 group-open/select:invalid:ring-3",
          "pressed:*:data-[slot=icon]:text-(--btn-icon-active) *:data-[slot=icon]:-mx-0.5 *:data-[slot=icon]:my-0.5 *:data-[slot=icon]:size-5 *:data-[slot=icon]:shrink-0 *:data-[slot=icon]:self-center *:data-[slot=icon]:text-(--btn-icon) hover:*:data-[slot=icon]:text-(--btn-icon-active)/90 focus-visible:*:data-[slot=icon]:text-(--btn-icon-active)/80 sm:*:data-[slot=icon]:my-1 sm:*:data-[slot=icon]:size-4 forced-colors:[--btn-icon:ButtonText] forced-colors:hover:[--btn-icon:ButtonText]",
          "*:data-[slot=loader]:-mx-0.5 *:data-[slot=loader]:my-0.5 *:data-[slot=loader]:size-5 *:data-[slot=loader]:shrink-0 *:data-[slot=loader]:self-center *:data-[slot=loader]:text-(--btn-icon) sm:*:data-[slot=loader]:my-1 sm:*:data-[slot=loader]:size-4",
          "forced-colors:group-invalid/select:inset-ring-[Mark] forced-colors:group-focus/select:inset-ring-[Highlight] forced-colors:group-focus/select:group-invalid/select:inset-ring-[Mark]",
          className,
        ]),
      )}
    >
      {(values) => (
        <>
          {props.prefix && (
            <span className="text-muted-fg">{props.prefix}</span>
          )}
          {typeof children === "function" ? children(values) : children}

          {!children && (
            <>
              <SelectValue
                className={twJoin([
                  "data-placeholder:text-muted-fg grid flex-1 grid-cols-[auto_1fr] items-center truncate sm:text-sm/6 [&_[slot=description]]:hidden",
                  "has-data-[slot=avatar]:gap-x-2 has-data-[slot=icon]:gap-x-2",
                  "*:data-[slot=icon]:size-4.5 sm:*:data-[slot=icon]:size-4",
                  "*:data-[slot=avatar]:*:size-5 *:data-[slot=avatar]:size-5 sm:*:data-[slot=avatar]:*:size-4.5 sm:*:data-[slot=avatar]:size-4.5",
                ])}
                data-slot="select-value"
              />
              <IconChevronsY
                className="text-muted-fg group-open/select:text-fg -mr-1 shrink-0 group-disabled/select:opacity-50 sm:mr-0"
                data-slot="chevron"
              />
            </>
          )}
        </>
      )}
    </Button>
  )
}

const SelectSection = DropdownSection
const SelectSeparator = DropdownSeparator
const SelectLabel = DropdownLabel
const SelectDescription = DropdownDescription
const SelectOption = DropdownItem

Select.Description = SelectDescription
Select.Option = SelectOption
Select.Label = SelectLabel
Select.Separator = SelectSeparator
Select.Section = SelectSection
Select.Trigger = SelectTrigger
Select.List = SelectList

export { Select }
export type { SelectProps, SelectTriggerProps }
