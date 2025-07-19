import type {
  ListBoxItemProps,
  SectionProps,
  SeparatorProps,
  TextProps,
} from "react-aria-components"

import { IconCheck } from "@intentui/icons"
import {
  Collection,
  composeRenderProps,
  Header,
  ListBoxItem as ListBoxItemPrimitive,
  ListBoxSection,
  Separator,
  Text,
} from "react-aria-components"
import { twMerge } from "tailwind-merge"
import { tv } from "tailwind-variants"

import { Keyboard } from "./keyboard"

const dropdownItemStyles = tv({
  base: [
    "[--mr-icon:--spacing(2)] sm:[--mr-icon:--spacing(1.5)]",
    "col-span-full grid grid-cols-[auto_1fr_1.5rem_0.5rem_auto] px-3 py-2 supports-[grid-template-columns:subgrid]:grid-cols-subgrid sm:px-2.5 sm:py-1.5",
    "not-has-[[slot=description]]:items-center has-[[slot=description]]:**:data-[slot=check-indicator]:mt-[1.5px]",
    "group text-fg relative cursor-default rounded-[calc(var(--radius-lg)-1px)] text-base/6 outline-0 select-none sm:text-sm/6",
    "**:data-[slot=avatar]:mr-(--mr-icon) **:data-[slot=avatar]:size-6 **:data-[slot=avatar]:*:mr-1.5 **:data-[slot=avatar]:*:size-6 sm:**:data-[slot=avatar]:size-5 sm:**:data-[slot=avatar]:*:size-5",
    "**:data-[slot=icon]:text-muted-fg *:data-[slot=icon]:mr-(--mr-icon) **:data-[slot=icon]:size-5 **:data-[slot=icon]:shrink-0 sm:**:data-[slot=icon]:size-4",
    "[&>[slot=label]+[data-slot=icon]]:absolute [&>[slot=label]+[data-slot=icon]]:right-1",
    "data-danger:text-danger data-danger:**:data-[slot=icon]:text-danger/60",
    "forced-color-adjust-none forced-colors:text-[CanvasText] forced-colors:**:data-[slot=icon]:text-[CanvasText] forced-colors:group-focus:**:data-[slot=icon]:text-[CanvasText]",
  ],
  variants: {
    isDanger: {
      true: [
        "text-danger focus:text-danger **:data-[slot=icon]:text-danger/70 focus:**:data-[slot=icon]:text-danger",
        "focus:*:[[slot=description]]:text-danger/80 focus:*:[[slot=label]]:text-danger",
        "focus:bg-danger/10 focus:text-danger focus:**:data-[slot=icon]:text-danger forced-colors:focus:text-[Mark]",
      ],
    },
    isDisabled: {
      true: "text-muted-fg forced-colors:text-[GrayText]",
    },
    isFocused: {
      true: [
        "**:data-[slot=icon]:text-accent-fg **:[kbd]:text-accent-fg",
        "bg-accent text-accent-fg forced-colors:bg-[Highlight] forced-colors:text-[HighlightText]",
        "[&_.text-muted-fg]:text-accent-fg/80 *:[[slot=description]]:text-accent-fg *:[[slot=label]]:text-accent-fg",
      ],
    },
    isHovered: {
      true: [
        "**:data-[slot=icon]:text-accent-fg **:[kbd]:text-accent-fg",
        "bg-accent text-accent-fg forced-colors:bg-[Highlight] forced-colors:text-[HighlightText]",
        "[&_.text-muted-fg]:text-accent-fg/80 *:[[slot=description]]:text-accent-fg *:[[slot=label]]:text-accent-fg",
      ],
    },
    isSelected: {
      true: "**:data-[slot=icon]:text-accent-fg **:data-[slot=avatar]:hidden **:data-[slot=avatar]:*:hidden **:data-[slot=icon]:hidden",
    },
  },
})

const dropdownSectionStyles = tv({
  slots: {
    header:
      "text-muted-fg col-span-full px-3.5 py-2 text-sm/6 font-medium sm:px-3 sm:py-1.5 sm:text-xs/5",
    section: "col-span-full grid grid-cols-[auto_1fr]",
  },
})

const { header, section } = dropdownSectionStyles()

type DropdownSectionProps<T> = SectionProps<T> & {
  title?: string
}

const DropdownSection = <T extends object>({
  children,
  className,
  ...props
}: DropdownSectionProps<T>) => {
  return (
    <ListBoxSection className={section({ className })}>
      {"title" in props && <Header className={header()}>{props.title}</Header>}
      <Collection items={props.items}>{children}</Collection>
    </ListBoxSection>
  )
}

type DropdownItemProps = ListBoxItemProps

const DropdownItem = ({ children, className, ...props }: DropdownItemProps) => {
  const textValue = typeof children === "string" ? children : undefined
  return (
    <ListBoxItemPrimitive
      className={composeRenderProps(className, (className, renderProps) =>
        dropdownItemStyles({ ...renderProps, className }),
      )}
      textValue={textValue}
      {...props}
    >
      {composeRenderProps(children, (children, { isSelected }) => (
        <>
          {isSelected && (
            <IconCheck className="-mx-1 mr-1.5" data-slot="check-indicator" />
          )}
          {typeof children === "string" ? (
            <DropdownLabel>{children}</DropdownLabel>
          ) : (
            children
          )}
        </>
      ))}
    </ListBoxItemPrimitive>
  )
}

type DropdownLabelProps = TextProps & {
  ref?: React.Ref<HTMLDivElement>
}

const DropdownLabel = ({ className, ref, ...props }: DropdownLabelProps) => (
  <Text
    className={twMerge("col-start-2", className)}
    ref={ref}
    slot="label"
    {...props}
  />
)

type DropdownDescriptionProps = TextProps & {
  ref?: React.Ref<HTMLDivElement>
}

const DropdownDescription = ({
  className,
  ref,
  ...props
}: DropdownDescriptionProps) => (
  <Text
    className={twMerge("text-muted-fg col-start-2 text-sm", className)}
    ref={ref}
    slot="description"
    {...props}
  />
)

const DropdownSeparator = ({ className, ...props }: SeparatorProps) => (
  <Separator
    className={twMerge("bg-fg/10 col-span-full -mx-1 my-1 h-px", className)}
    orientation="horizontal"
    {...props}
  />
)

const DropdownKeyboard = ({
  className,
  ...props
}: React.ComponentProps<typeof Keyboard>) => {
  return (
    <Keyboard
      classNames={{
        base: twMerge(
          "absolute right-2 pl-2 group-hover:text-primary-fg group-focus:text-primary-fg",
          className,
        ),
      }}
      {...props}
    />
  )
}

/**
 * Note: This is not exposed component, but it's used in other components to render dropdowns.
 * @internal
 */
export type {
  DropdownDescriptionProps,
  DropdownItemProps,
  DropdownLabelProps,
  DropdownSectionProps,
}
export {
  DropdownDescription,
  DropdownItem,
  dropdownItemStyles,
  DropdownKeyboard,
  DropdownLabel,
  DropdownSection,
  dropdownSectionStyles,
  DropdownSeparator,
}
