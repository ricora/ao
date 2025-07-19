import type {
  TabListProps as TabListPrimitiveProps,
  TabPanelProps as TabPanelPrimitiveProps,
  TabProps as TabPrimitiveProps,
  TabsProps as TabsPrimitiveProps,
} from "react-aria-components"

import { composeTailwindRenderProps } from "@/lib/primitive"
import {
  composeRenderProps,
  TabList as TabListPrimitive,
  TabPanel as TabPanelPrimitive,
  Tab as TabPrimitive,
  Tabs as TabsPrimitive,
} from "react-aria-components"
import { twMerge } from "tailwind-merge"

type TabsProps = TabsPrimitiveProps & {
  ref?: React.RefObject<HTMLDivElement>
}
const Tabs = ({ className, ref, ...props }: TabsProps) => {
  return (
    <TabsPrimitive
      className={composeTailwindRenderProps(
        className,
        "group/tabs orientation-vertical:w-[800px] orientation-vertical:flex-row orientation-horizontal:flex-col flex gap-4 forced-color-adjust-none",
      )}
      ref={ref}
      {...props}
    />
  )
}

type TabListProps<T extends object> = TabListPrimitiveProps<T> & {
  ref?: React.RefObject<HTMLDivElement>
}
const TabList = <T extends object>({
  className,
  ref,
  ...props
}: TabListProps<T>) => {
  return (
    <TabListPrimitive
      ref={ref}
      {...props}
      className={composeRenderProps(className, (className, { orientation }) =>
        twMerge([
          "flex forced-color-adjust-none",
          orientation === "horizontal" &&
            "border-border flex-row gap-x-5 border-b",
          orientation === "vertical" && "flex-col items-start gap-y-4 border-l",
          className,
        ]),
      )}
    />
  )
}

type TabProps = TabPrimitiveProps & {
  ref?: React.RefObject<HTMLButtonElement>
}
const Tab = ({ children, className, ref, ...props }: TabProps) => {
  return (
    <TabPrimitive
      ref={ref}
      {...props}
      className={composeTailwindRenderProps(className, [
        "text-fg hover:text-fg relative flex cursor-default items-center rounded-full text-sm font-medium whitespace-nowrap outline-hidden transition *:data-[slot=icon]:mr-2 *:data-[slot=icon]:size-4",
        "group-orientation-vertical/tabs:w-full group-orientation-vertical/tabs:py-0 group-orientation-vertical/tabs:pr-2 group-orientation-vertical/tabs:pl-4",
        "group-orientation-horizontal/tabs:pb-3",
        "selected:text-fg text-muted-fg focus:ring-0",
        "disabled:opacity-50",
        "href" in props && "cursor-pointer",
      ])}
    >
      {({ isSelected }) => (
        <>
          {children}
          {isSelected && (
            <span
              className={twMerge(
                "bg-fg absolute rounded",
                "group-orientation-horizontal/tabs:-bottom-px group-orientation-horizontal/tabs:inset-x-0 group-orientation-horizontal/tabs:h-0.5 group-orientation-horizontal/tabs:w-full",
                "group-orientation-vertical/tabs:left-0 group-orientation-vertical/tabs:h-[calc(100%-10%)] group-orientation-vertical/tabs:w-0.5 group-orientation-vertical/tabs:transform",
              )}
              data-slot="selected-indicator"
            />
          )}
        </>
      )}
    </TabPrimitive>
  )
}

type TabPanelProps = TabPanelPrimitiveProps & {
  ref?: React.RefObject<HTMLDivElement>
}
const TabPanel = ({ className, ref, ...props }: TabPanelProps) => {
  return (
    <TabPanelPrimitive
      {...props}
      className={composeTailwindRenderProps(
        className,
        "text-fg flex-1 text-sm focus-visible:outline-hidden",
      )}
      ref={ref}
    />
  )
}

export type { TabListProps, TabPanelProps, TabProps, TabsProps }
export { Tab, TabList, TabPanel, Tabs }
