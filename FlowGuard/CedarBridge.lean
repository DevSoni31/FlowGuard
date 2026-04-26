namespace FlowGuard

structure CedarPrincipal where
  name : String
  deriving Repr

structure CedarAction where
  name : String
  deriving Repr

structure CedarResource where
  name : String
  deriving Repr

end FlowGuard
