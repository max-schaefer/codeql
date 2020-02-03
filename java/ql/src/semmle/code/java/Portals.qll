import java
private import semmle.code.java.dispatch.VirtualDispatch

private newtype TPortal =
  MkPackagePortal(Package pkg) or
  MkMemberPortal(Portal base, string memb) {
    MemberPortal::packageMember(base, memb, _) or
    MemberPortal::typeMember(base, memb, _)
  } or
  MkInstancePortal(Portal base) { InstancePortal::instance(base, _) } or
  MkParameterPortal(Portal base, int i) { ParameterPortal::parameter(base, i, _) } or
  MkReturnPortal(Portal base) { ReturnPortal::return(base, _) }

class Portal extends TPortal {
  /**
   * Gets an exit node for this portal, that is, a node from which data
   * that comes through the portal emerges.
   */
  abstract Top getAnExitNode();

  /**
   * Gets an entry node for this portal, that is, a node through which data
   * enters the portal.
   */
  abstract Top getAnEntryNode();

  /**
   * Gets a textual representation of this portal.
   *
   * Different portals must have different `toString`s, so the result of
   * this predicate can be used to uniquely identify a portal.
   */
  abstract string toString();
}

class PackagePortal extends Portal, MkPackagePortal {
  Package pkg;

  PackagePortal() { this = MkPackagePortal(pkg) }

  Package getPackage() { result = pkg }

  override Top getAnExitNode() { none() }

  override Top getAnEntryNode() { none() }

  override string toString() { result = "(root " + pkg.getName() + ")" }
}

class MemberPortal extends Portal, MkMemberPortal {
  Portal base;
  string memb;

  MemberPortal() { this = MkMemberPortal(base, memb) }

  override Top getAnExitNode() {
    MemberPortal::packageMember(base, memb, result.(TypeAccess).getType())
    or
    MemberPortal::typeMember(base, memb, result.(TypeAccess).getType())
    or
    MemberPortal::typeMember(base, memb, result.(MethodAccess).getMethod())
    or
    MemberPortal::typeMember(base, memb, result.(FieldAccess).getField())
  }

  override Top getAnEntryNode() {
    MemberPortal::packageMember(base, memb, result)
    or
    MemberPortal::typeMember(base, memb, result)
    or
    exists(Field f | MemberPortal::typeMember(base, memb, f) | result = f.getAnAssignedValue())
  }

  override string toString() { result = "(member " + memb + " " + base + ")" }
}

module MemberPortal {
  predicate packageMember(PackagePortal base, string name, RefType tp) {
    tp.getPackage() = base.getPackage() and
    name = "type:" + tp.getName()
  }

  predicate typeMember(Portal base, string name, Member m) {
    exists(Portal declTypePortal | declTypePortal.getAnEntryNode() = m.getDeclaringType() |
      m.isStatic() and
      base = declTypePortal
      or
      base.(InstancePortal).getBasePortal() = declTypePortal
    ) and
    (
      name = "field:" + m.(Field).getName()
      or
      name = "callable:" + m.(Callable).getSignature()
      or
      name = "type:" + m.(Type).getName()
    )
  }
}

class InstancePortal extends Portal, MkInstancePortal {
  Portal base;

  InstancePortal() { this = MkInstancePortal(base) }

  Portal getBasePortal() { result = base }

  override Expr getAnExitNode() {
    result.getType().(RefType).getASupertype*() = base.getAnEntryNode()
  }

  override Top getAnEntryNode() { none() }

  override string toString() { result = "(instance " + base + ")" }
}

module InstancePortal {
  predicate instance(Portal base, ClassOrInterface tp) { tp = base.getAnEntryNode() }
}

class ParameterPortal extends Portal, MkParameterPortal {
  Portal base;
  int i;

  ParameterPortal() { this = MkParameterPortal(base, i) }

  Parameter getParameter() { ParameterPortal::parameter(base, i, result) }

  override Expr getAnExitNode() { result = getParameter().getAnAccess() }

  override Expr getAnEntryNode() {
    exists(Call c | viableCallable(c) = getParameter().getCallable() | result = c.getArgument(i))
  }

  override string toString() { result = "(parameter " + i + " " + base + ")" }
}

module ParameterPortal {
  predicate parameter(Portal base, int i, Parameter p) {
    base.getAnEntryNode().(Callable).getParameter(i) = p
  }
}

class ReturnPortal extends Portal, MkReturnPortal {
  Portal base;

  ReturnPortal() { this = MkReturnPortal(base) }

  Method getMethod() { ReturnPortal::return(base, result) }

  override MethodAccess getAnExitNode() {
    viableCallable(result) = getMethod()
  }

  override Expr getAnEntryNode() {
    exists(ReturnStmt ret |
      ret.getEnclosingCallable() = getMethod() and
      result = ret.getResult()
    )
  }

  override string toString() { result = "(return " + base + ")" }
}

module ReturnPortal {
  predicate return(Portal base, Method m) {
    m = base.getAnEntryNode() and
    not m.getReturnType() instanceof VoidType
  }
}
