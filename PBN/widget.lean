import Lean
import PBN.AndORGraph
open Lean Widget

@[widget_module]
def helloWidget: Widget.Module where
  javascript := "
    import * as React from 'react';
    export default function(props) {
      const name = props.name || 'world'
      return React.createElement('p', {}, 'Hello ' + name + '!')
    }"

structure HelloWidgetProps where
  name? : Option String := none
  deriving Server.RpcEncodable

#widget helloWidget with { name? := "<your name here>" : HelloWidgetProps }
