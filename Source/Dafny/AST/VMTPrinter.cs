using System;
using System.IO;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;
using System.Linq;
using System.Diagnostics;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {

  public class DafnyDatatype {
    /*
    EXAMPLE:

    Whatever = SomeCtor(id:int, semaphore:bool, servers:set<Server>, c: Client)

    DafnyDatatype{
      USER_DEFINED
      name=Whatever
      members{
        DafnyDatatype{
          INT
          name=id
        },
        DafnyDatatype{
          BOOL,
          name=semaphore
        },
        DafnyDatatype{
          SET,
          name=servers
          Subtype=(DafnyDatatype)Server
        },
        DafnyDatatype{
          USER_DEFINED,
          name=c
          Subtype=(DafnyDatatype)Client
        }
      }
    }
  */

    public enum TYPE {
      BOOL,
      INT,
      SET,
      USER_DEFINED,
    }
    public string Name;

    public TYPE T;

    // Used when t == USER_DEFINED & new definition
    public List<DafnyDatatype> Members = null;

    // Used when t == SET ||
    public DafnyDatatype Subtype = null; // DafnyDatatypes[this.Subtype]
  }

  public class VMTPrinter : Printer {

    private string VMT_HEADER = @"; Typecast bit to bool
(define-sort bool_type () (_ BitVec 1))
(define-fun bv_false () bool_type (_ bv0 1))
(define-fun bv_true  () bool_type (_ bv1 1))
(define-fun is_bool ((x bool_type)) Bool (or (= x bv_true) (= x bv_false))))
";

    private string STATE_MACHINE_DATATYPE_NAME = "DafnyState";
    private string STATE_MACHINE_INIT_PRED_NAME = "Init";
    private string STATE_MACHINE_NEXT_PRED_NAME = "Next";
    private string STATE_MACHINE_SAFETY_PRED_NAME = "Safety";
    private string STATE_MACHINE_ACTION_PREFIX = "Action";

    public Dictionary<string, int> Instances;
    public HashSet<int> TypeLengthSet = new HashSet<int> { 0, 1 };
    public Predicate InitPredicate = null;
    public Predicate NextPredicate = null;
    public Predicate InvariantPredicate = null;

    public string PrevName = null;

    public string NextName = null;

    // maps name of relation to names of datatypes
    public Dictionary<string, List<string>> RelationDatatypeParams = new Dictionary<string, List<string>>();

    public Dictionary<string, List<string>> RelationCombos = new Dictionary<string, List<string>>();

    public List<Predicate> ActionPredicates = new List<Predicate>();

    public Dictionary<string, Predicate> OtherPredicates = new Dictionary<string, Predicate>();

    public Dictionary<string, DafnyDatatype> DafnyDatatypes = new Dictionary<string, DafnyDatatype>();

    public VMTPrinter(TextWriter wr,
                      Dictionary<string, int> datatypeInstanceCounts,
                      DafnyOptions.PrintModes printMode = DafnyOptions.PrintModes.Everything)
        : base(wr, printMode) {
      Instances = datatypeInstanceCounts;
    }

    public override void PrintProgram(Program prog, bool afterResolver) {
      Console.WriteLine("Creating finite instance in VMT.");

      wr.Write(VMT_HEADER);

      ParseDatatypes(prog);
      ParsePredicates(prog);
      BuildStates();
      BuildInit();
      BuildActions();
      DeclareActionsAndTransitionRelations();
      BuildNext();
      BuildSafety();

      wr.Flush();
    }

    public void ParseDatatypes(Program prog) {
      wr.WriteLine("\n; Define and enumerate transition system parameters");

      int numFoundFinitizedDatatypes = 0;

      foreach (TopLevelDecl d in prog.DefaultModuleDef.TopLevelDecls) {
        if (d is DatatypeDecl) {
          var dd = (DatatypeDecl)d;
          var name = dd.Name;

          if (name == STATE_MACHINE_DATATYPE_NAME) {
            // Dealing with outer state machine datatype
            ParseDatatypeCtors(dd);
            // Constrain DafnyState creation
            DafnyDatatype dafnyState = DafnyDatatypes[STATE_MACHINE_DATATYPE_NAME];
            Debug.Assert(dafnyState.Name == STATE_MACHINE_DATATYPE_NAME,
                         "All-encompassing DafnyDatatype has incorrect name '" + dafnyState.Name + "'");
            Debug.Assert(dafnyState.T == DafnyDatatype.TYPE.USER_DEFINED,
                         "All-encompassing DafnyDatatype has incorrect DafnyDatatype.TYPE '" + dafnyState.T + "'");
            foreach (DafnyDatatype member in dafnyState.Members) {
              Debug.Assert(member.T == DafnyDatatype.TYPE.SET && member.Subtype.T == DafnyDatatype.TYPE.USER_DEFINED,
                           "All-encompassing datatype '" + STATE_MACHINE_DATATYPE_NAME + "' can only take as parameters sets of finitized datatypes");
            }
          } else if (Instances.ContainsKey(name)) {
            // Dealing with one of our finitized datatypes
            ++numFoundFinitizedDatatypes;

            var l = Convert.ToInt32(Math.Log2(Instances[name]));
            while (TypeLengthSet.Contains(l)) {
              l += 1;
            }
            TypeLengthSet.Add(l);
            wr.WriteLine("(define-sort " + name + "_type () (_ BitVec " + l + "))");
            var typeCheckString = "";
            for (int i = 0; i < Instances[name]; ++i) {
              wr.WriteLine("(define-fun " + name + i + " () " + name + "_type (_ bv" + i + " " + l + "))");
              typeCheckString += "(= " + name + " " + name + i + ") ";
            }
            wr.WriteLine("(define-fun is_" + name + " ((" + name + " " + name + "_type)) Bool (or " + typeCheckString + "))");

            ParseDatatypeCtors(dd);
          } else {
            Debug.Assert(false, "Datatype '" + name + "' found in Dafny program but no finitization provided on command line.");
          }
        }
      }

      Debug.Assert(DafnyDatatypes.ContainsKey(STATE_MACHINE_DATATYPE_NAME), "No definition found for state machine datatype '" + STATE_MACHINE_DATATYPE_NAME + "'");
      Debug.Assert(numFoundFinitizedDatatypes == Instances.Count, "Command line contains finitized datatype(s) not found in Dafny program.");
    }

    public void ParseDatatypeCtors(DatatypeDecl dd) {
      Debug.Assert(dd.Ctors.Count == 1, "Datatype '" + dd.Name + "' has more than one constructor. This is not currently handled.");

      DatatypeCtor ctor = dd.Ctors[0];
      DafnyDatatype def = new DafnyDatatype();
      def.T = DafnyDatatype.TYPE.USER_DEFINED;
      def.Name = dd.Name;
      def.Members = new List<DafnyDatatype>();

      var datatypeParams = new List<string>();
      foreach (Formal f in ctor.Formals) {
        string typeName = f.Type.ToString();

        DafnyDatatype member = new DafnyDatatype();
        member.Name = f.Name;
        if (DafnyDatatypes.ContainsKey(typeName)) {
          member.T = DafnyDatatype.TYPE.USER_DEFINED;
          member.Subtype = DafnyDatatypes[typeName];
        } else if (typeName.StartsWith("set")) {
          member.T = DafnyDatatype.TYPE.SET;
          string subtype = f.Type.TypeArgs[0].ToString();
          Debug.Assert(DafnyDatatypes.ContainsKey(subtype), "DafnyDatatype subtype '" + subtype + "' not found in user-defined datatype list");
          member.Subtype = DafnyDatatypes[subtype];
        } else {
          switch (typeName) {
            case "bool":
              member.T = DafnyDatatype.TYPE.BOOL;
              break;
            case "int":
              member.T = DafnyDatatype.TYPE.INT;
              break;
            default:
              Debug.Assert(false, "unsupported datatype subtype: " + typeName);
              break;
          }
        }

        def.Members.Add(member);
      }
      DafnyDatatypes.Add(dd.Name, def);
    }

    public void ParsePredicates(Program prog) {
      foreach (TopLevelDecl d in prog.DefaultModuleDef.TopLevelDecls) {
        if (d is ClassDecl) {
          ClassDecl cl = (ClassDecl)d;
          foreach (MemberDecl mem in cl.Members) {
            if (mem is Function) {
              Function f = (Function)mem;
              if (f is Predicate) {
                ParsePredicate((Predicate)f);
              }
            }
          }
        }
      }

      Debug.Assert(InitPredicate != null, "Dafny program is missing the '" + STATE_MACHINE_INIT_PRED_NAME + "' predicate.");
      Debug.Assert(NextPredicate != null, "Dafny program is missing the '" + STATE_MACHINE_NEXT_PRED_NAME + "' predicate.");
      Debug.Assert(InvariantPredicate != null, "Dafny program is missing the '" + STATE_MACHINE_SAFETY_PRED_NAME + "' predicate.");
    }

    public void ParsePredicate(Predicate pred) {
      var name = pred.Name;

      if (name == STATE_MACHINE_INIT_PRED_NAME) {
        // Dealing with Init
        Debug.Assert(pred.Formals.Count == 1 && pred.Formals[0].Type.ToString() == STATE_MACHINE_DATATYPE_NAME,
                     "Init predicate must take exactly one parameter, of type " + STATE_MACHINE_DATATYPE_NAME);
        InitPredicate = pred;
      } else if (name == STATE_MACHINE_NEXT_PRED_NAME) {
        // Dealing with Next
        Debug.Assert(pred.Formals.Count == 2
                     && pred.Formals[0].Type.ToString() == STATE_MACHINE_DATATYPE_NAME
                     && pred.Formals[1].Type.ToString() == STATE_MACHINE_DATATYPE_NAME,
                     "Next predicate must take exactly two parameters, of type " + STATE_MACHINE_DATATYPE_NAME
                     + ". The first represents the current/previous state, the second represents the next state.");
        NextPredicate = pred;
      } else if (name == STATE_MACHINE_SAFETY_PRED_NAME) {
        Debug.Assert(pred.Formals.Count == 1, "Invariant predicate must take exactly one parameter, of type " + STATE_MACHINE_DATATYPE_NAME);
        InvariantPredicate = pred;
      } else if (name.StartsWith(STATE_MACHINE_ACTION_PREFIX) && name != STATE_MACHINE_ACTION_PREFIX) {
        // Dealing with an action
        Debug.Assert(pred.Formals.Count == 2
                     && pred.Formals[0].Type.ToString() == STATE_MACHINE_DATATYPE_NAME
                     && pred.Formals[1].Type.ToString() == STATE_MACHINE_DATATYPE_NAME,
                     "Action predicates must take exactly two parameters, of type " + STATE_MACHINE_DATATYPE_NAME
                     + ". The first represents the current/previous state, the second represents the next state.");
        ActionPredicates.Add(pred);
      } else {
        OtherPredicates.Add(name, pred);
      }
    }

    public void BuildStates() {
      wr.WriteLine("\n; Declare transition system states");

      foreach ((string typename, DafnyDatatype typeobj) in DafnyDatatypes) {
        // Parse DafnyState slightly differently
        if (typename == STATE_MACHINE_DATATYPE_NAME) {
          foreach (DafnyDatatype m in typeobj.Members) {
            Debug.Assert(m.T == DafnyDatatype.TYPE.SET && m.Subtype.T == DafnyDatatype.TYPE.USER_DEFINED,
                         "All-encompassing datatype '" + STATE_MACHINE_DATATYPE_NAME + "' can only take as parameters sets of finitized datatypes");

            for (int setSubtypeInstIndx = 0; setSubtypeInstIndx < Instances[m.Subtype.Name]; ++setSubtypeInstIndx) {
              string str = STATE_MACHINE_DATATYPE_NAME + "_" + m.Name + "_" + m.Subtype.Name + setSubtypeInstIndx;
              wr.WriteLine("(define-fun {0} () bool_type bv_true)", str);
              wr.WriteLine("(define-fun {0}_next () bool_type bv_true)", str);
            }
          }
          continue;
        }

        for (int i = 0; i < Instances[typename]; ++i) {
          foreach (DafnyDatatype m in typeobj.Members) {

            // ID fields should not be considered mutable state
            if (m.Name == "id") {
              Debug.Assert(m.T == DafnyDatatype.TYPE.INT, "Special 'id' field in finitized datatypes must be of type int");
              wr.WriteLine("(define-fun {0}{1}_id () Int {1})", typename, i);
              wr.WriteLine("(define-fun {0}{1}_id_next () Int {1})", typename, i);
              continue;
            }

            string stateVariableName = typename + i + "_" + m.Name;
            string stateVariableType = "";
            switch (m.T) {
              case DafnyDatatype.TYPE.INT:
                stateVariableType = "Int";
                break;
              case DafnyDatatype.TYPE.BOOL:
                stateVariableType = "bool_type";
                break;
              case DafnyDatatype.TYPE.SET:
                // Create a VMT object for every possible membership in the set.
                // We do it this way because the model checker seems to require that arrays be initialized
                // as whole constants (which we can't easily constrain in Dafny) for the model checker to
                // be able to check initial values at specific indices.
                for (int setSubtypeInstIndx = 0; setSubtypeInstIndx < Instances[m.Subtype.Name]; ++setSubtypeInstIndx) {
                  string str = stateVariableName + "_" + m.Subtype.Name + setSubtypeInstIndx;
                  wr.WriteLine("(declare-fun {0} () bool_type)", str);
                  wr.WriteLine("(declare-fun {0}_next () bool_type)", str);
                  wr.WriteLine("(define-fun .{0} () bool_type (! {0} :next {0}_next))", str);
                }
                continue;
              case DafnyDatatype.TYPE.USER_DEFINED:
                stateVariableType = m.Subtype.Name + "_type";
                break;
              default:
                Debug.Assert(false, "unexpected member type");
                break;
            }
            wr.WriteLine("(declare-fun {0} () {1})", stateVariableName, stateVariableType);
            wr.WriteLine("(declare-fun {0}_next () {1})", stateVariableName, stateVariableType);
            wr.WriteLine("(define-fun .{0} () {1} (! {0} :next {0}_next))", stateVariableName, stateVariableType);
          }
        }
      }
    }

    public void BuildInit() {
      PrevName = InitPredicate.Formals[0].Name;
      NextName = null;
      wr.Write("\n; Initial state\n");
      wr.Write("(define-fun .init () Bool (! ");
      wr.Write("(= ");
      wr.Write(InstantiateExpr(InitPredicate.Body));
      wr.Write(" bv_true)");
      wr.Write(" :init true))\n");
      PrevName = null;
      NextName = null;
    }

    public void BuildActions() {
      foreach (Predicate pred in ActionPredicates) {
        PrevName = pred.Formals[0].Name;
        NextName = pred.Formals[1].Name;
        wr.Write("\n(define-fun {0}_fun () Bool ", pred.Name);
        wr.Write("(= ");
        wr.Write(InstantiateExpr(pred.Body));
        wr.Write(" bv_true)");
        wr.Write(")\n");
      }
      PrevName = null;
      NextName = null;
    }

    public void DeclareActionsAndTransitionRelations() {
      wr.WriteLine("\n; Declare actions");

      var l = Convert.ToInt32(Math.Log2(ActionPredicates.Count));
      while (TypeLengthSet.Contains(l)) {
        l += 1;
      }
      TypeLengthSet.Add(l);

      wr.WriteLine("(define-sort action_type () (_ BitVec {0}))", l);
      for (int i = 0; i < ActionPredicates.Count; ++i) {
        wr.WriteLine("(define-fun {0}() action_type (_ bv{1} {2}))", ActionPredicates[i].Name, i, l);
      }

      wr.WriteLine("\n; Transition relation");
      wr.WriteLine("(declare-fun action () action_type)");
    }

    public void BuildNext() {
      string checkActions = "";
      string checkNoAction = " (=> (not (or";
      foreach (Predicate pred in ActionPredicates) {
        checkActions += " (=> (= action " + pred.Name + ") (and " + pred.Name + "_fun))"; // TODO add parantheses and stuff if we add parameters to actions
        checkNoAction += " (= action " + pred.Name + ")";
      }
      checkNoAction += ")) (and";

      foreach ((string typename, DafnyDatatype typeobj) in DafnyDatatypes) {
        // ignore top-level state machine object
        if (typename == STATE_MACHINE_DATATYPE_NAME) {
          continue;
        }

        for (int i = 0; i < Instances[typename]; ++i) {
          foreach (DafnyDatatype m in typeobj.Members) {
            if (m.Name == "id") {
              // ID fields are not mutable state
              continue;
            } else {
              // ensure that state variable does not change on transition
              string stateVariableName = typename + i + "_" + m.Name;
              if (m.T == DafnyDatatype.TYPE.SET) {
                for (int j = 0; j < Instances[m.Subtype.Name]; ++j) {
                  string s = stateVariableName + "_" + m.Subtype.Name + j;
                  checkNoAction += " (= " + s + " " + s + "_next)";
                }
              } else {
                checkNoAction += " (= " + stateVariableName + " " + stateVariableName + "_next)";
              }
            }
          }
        }
      }
      checkNoAction += "))";

      wr.WriteLine("(define-fun .trans () Bool (! (and" + checkActions + checkNoAction + ") :trans true))");
    }

    public void BuildSafety() {
      PrevName = InvariantPredicate.Formals[0].Name;
      wr.Write("(define-fun .prop () Bool (! ");
      wr.Write("(= ");
      wr.Write(InstantiateExpr(InvariantPredicate.Body));
      wr.Write(" bv_true)");
      wr.Write(" :invar-property 0))\n");
      PrevName = null;
    }

    public string InstantiateExpr(Expression e, Dictionary<string, string> replace = null) {
      if (e is BinaryExpr) {
        return InstantiateBinaryExpr(e, replace);
      } else if (e is UnaryExpr) {
        return InstantiateUnary(e, replace);
      } else if (e is ForallExpr) {
        return InstantiateForall(e, replace);
      } else if (e is ExistsExpr) {
        return InstantiateExists(e, replace);
      } else if (e is LiteralExpr) {
        return InstantiateLiteral(e, replace);
      } else if (e is ParensExpression) {
        return InstantiateExpr(Expression.StripParens(e), replace);
      } else if (e is FunctionCallExpr) {
        return InstantiateFunctionCallExpr(e, replace);
      } else if (e is ExprDotName) {
        return InstantiateExprDotNameExpr(e, replace);
      } else if (e is ApplySuffix) {
        return InstantiateApplySuffixExpr(e, replace);
      } else if (e is NameSegment) {
        return InstantiateNameSegment(e, replace);
      } else {
        return UnhandledCase(e, replace);
      }

    }
    public string InstantiateBinaryExpr(Expression e, Dictionary<string, string> replace = null) {
      Debug.Assert(e is BinaryExpr);
      var exp = (BinaryExpr)e;
      switch (exp.Op) {
        case BinaryExpr.Opcode.And:
          return InstantiateAnd(e, replace);
        case BinaryExpr.Opcode.Or:
          return InstantiateOr(e, replace);
        case BinaryExpr.Opcode.Imp:
          return InstantiateImplies(e, replace);
        case BinaryExpr.Opcode.Eq:
          return InstantiateEqual(e, replace);
        case BinaryExpr.Opcode.Neq:
          return InstantiateNotEqual(e, replace);
        case BinaryExpr.Opcode.In:
          return InstantiateInExpr(e, replace);
        case BinaryExpr.Opcode.NotIn:
          return InstantiateNotInExpr(e, replace);
        default:
          return UnhandledCase(e, replace);
      }
    }

    public string InstantiateForall(Expression e, Dictionary<string, string> replace = null) {
      Debug.Assert(e is ForallExpr);
      string retval = "";
      var exp = (ForallExpr)e;
      Expression body = exp.LogicalBody();

      if (replace == null) {
        replace = new Dictionary<string, string>();
      }

      List<Dictionary<string, string>> allcombs = new List<Dictionary<string, string>>();
      Dictionary<string, string> start = new Dictionary<string, string>();
      GenerateFinitizationHelper(ref allcombs, ref start, exp.BoundVars);

      // need to check variables, if of type datatype, then instantiate every instance in implies
      retval += "(ite ";
      retval += "(and ";
      // take body of expression and instantiate for all bounded variables
      for (int i = 0; i < allcombs.Count; ++i) {
        foreach (var (key, val) in allcombs[i]) {
          replace.Add(key, val);
        }
        retval += "(or (= ";

        retval += InstantiateExpr(body, replace);

        retval += " bv_true)) ";


        foreach (var (key, val) in allcombs[i]) {
          replace.Remove(key);
        }
      }

      retval += ")";
      retval += " bv_true bv_false)";
      return retval;
    }

    public string InstantiateExists(Expression e, Dictionary<string, string> replace = null) {
      Debug.Assert(e is ExistsExpr);
      string retval = "";
      var exp = (ExistsExpr)e;
      Expression body = exp.LogicalBody();

      if (replace == null) {
        replace = new Dictionary<string, string>();
      }

      List<Dictionary<string, string>> allcombs = new List<Dictionary<string, string>>();
      Dictionary<string, string> start = new Dictionary<string, string>();
      GenerateFinitizationHelper(ref allcombs, ref start, exp.BoundVars);

      // need to check variables, if of type datatype, then instantiate every instance in implies
      retval += "(ite ";
      retval += "(or ";
      // take body of expression and instantiate for all bounded variables
      for (int i = 0; i < allcombs.Count; ++i) {
        foreach (var (key, val) in allcombs[i]) {
          replace.Add(key, val);
        }
        retval += "(or (= ";
        retval += InstantiateExpr(body, replace);
        retval += " bv_true)) ";

        foreach (var (key, val) in allcombs[i]) {
          replace.Remove(key);
        }
      }

      retval += ")";
      retval += " bv_true bv_false)";
      return retval;
    }

    private void GenerateFinitizationHelper(ref List<Dictionary<string, string>> final, ref Dictionary<string, string> current, List<BoundVar> vars) {
      if (current.Count == vars.Count) {
        final.Add(new Dictionary<string, string>());
        foreach (var (key, val) in current) {
          final[final.Count - 1].Add(key, val);
        }
        return;
      }
      int size = current.Count;
      BoundVar v = vars[size];
      for (int i = 0; i < Instances[v.Type.ToString()]; ++i) {
        current.Add(v.Name, v.Type.ToString() + i);
        GenerateFinitizationHelper(ref final, ref current, vars);
        current.Remove(v.Name);
      }
    }

    public string InstantiateUnary(Expression e, Dictionary<string, string> replace = null) {
      if (e is UnaryOpExpr) {
        UnaryOpExpr exp = (UnaryOpExpr)e;
        switch (exp.Op) {
          case (UnaryOpExpr.Opcode.Not):
            return InstantiateNot(e, replace);
          default:
            return UnhandledCase(e, replace);
        }
      } else if (e is TypeUnaryExpr) {
        return UnhandledCase(e, replace);
      }
      return UnhandledCase(e, replace);
    }

    public string InstantiateNot(Expression e, Dictionary<string, string> replace = null) {
      UnaryOpExpr exp = (UnaryOpExpr)e;
      string retval = "(ite (= ";
      retval += InstantiateExpr(exp.E, replace);
      retval += " bv_true) bv_false bv_true)";
      return retval;
    }

    public string InstantiateLiteral(Expression e, Dictionary<string, string> replace = null) {
      LiteralExpr exp = (LiteralExpr)e;
      if (exp.Value is bool) {
        if ((bool)exp.Value) {
          return "bv_true";
        } else {
          return "bv_false";
        }
      }

      return UnhandledCase(e, replace);
    }


    public string UnhandledCase(Expression e, Dictionary<string, string> replace = null) {
      base.PrintExpression(e, false);
      FunctionCallExpr exp = (FunctionCallExpr)e;
      Debug.Assert(false, "unhandled expression");
      return "";
    }

    public string InstantiateAnd(Expression e, Dictionary<string, string> replace = null) {
      BinaryExpr exp = (BinaryExpr)e;
      Debug.Assert(exp.Op == BinaryExpr.Opcode.And);
      string retval = "(ite (and ";
      retval += "(= ";
      retval += InstantiateExpr(exp.E0, replace);
      retval += " bv_true) (= ";
      retval += InstantiateExpr(exp.E1, replace);
      retval += " bv_true)) bv_true bv_false)";
      return retval;
    }

    public string InstantiateOr(Expression e, Dictionary<string, string> replace = null) {
      BinaryExpr exp = (BinaryExpr)e;
      Debug.Assert(exp.Op == BinaryExpr.Opcode.Or);
      string retval = "(ite (or (= ";
      retval += InstantiateExpr(exp.E0, replace);
      retval += " bv_true) (= ";
      retval += InstantiateExpr(exp.E1, replace);
      retval += " bv_true)) bv_true bv_false)";
      return retval;
    }

    public string InstantiateImplies(Expression e, Dictionary<string, string> replace = null) {
      BinaryExpr exp = (BinaryExpr)e;
      Debug.Assert(exp.Op == BinaryExpr.Opcode.Imp);
      string retval = "(ite (=> (= ";
      retval += InstantiateExpr(exp.E0, replace);
      retval += " bv_true) (= ";
      retval += InstantiateExpr(exp.E1, replace);
      retval += " bv_true)) bv_true bv_false)";
      return retval;
    }

    public string InstantiateEqual(Expression e, Dictionary<string, string> replace = null) {
      BinaryExpr exp = (BinaryExpr)e;
      Debug.Assert(exp.Op == BinaryExpr.Opcode.Eq);
      string retval = "(ite (= ";
      retval += InstantiateExpr(exp.E0, replace);
      retval += " ";
      retval += InstantiateExpr(exp.E1, replace);
      retval += ") bv_true bv_false)";
      return retval;
    }

    public string InstantiateNotEqual(Expression e, Dictionary<string, string> replace = null) {
      BinaryExpr exp = (BinaryExpr)e;
      Debug.Assert(exp.Op == BinaryExpr.Opcode.Neq);
      string retval = "(ite (= ";
      retval += InstantiateExpr(exp.E0, replace);
      retval += " ";
      retval += InstantiateExpr(exp.E1, replace);
      retval += ") bv_false bv_true)";
      return retval;
    }

    public string InstantiateFunction(string name, List<Expression> args, Dictionary<string, string> replace = null) {
      Debug.Assert(replace != null || args.Count == 0, "the impossible happened! function not finitized!");
      Predicate p = OtherPredicates[name];
      string tempprev = PrevName;
      string tempnext = NextName;
      bool encountered_prev = false;
      bool encountered_next = false;
      Dictionary<string, string> diff_replace = new Dictionary<string, string>();

      for (int i = 0; i < args.Count(); ++i) {

        if (p.Formals[i].Name == PrevName) {
          PrevName = p.Formals[i].Name;
          encountered_prev = true;
          continue;
        } else if (p.Formals[i].Name == NextName) {
          NextName = p.Formals[i].Name;
          encountered_next = true;
          continue;
        }
        NameSegment n = (NameSegment)args[i];
        diff_replace.Add(p.Formals[i].Name, replace[n.Name]);
      }

      if (!encountered_next) {
        NextName = null;
      }
      if (!encountered_prev) {
        PrevName = null;
      }

      string retval = InstantiateExpr(p.Body, diff_replace);

      PrevName = tempprev;
      NextName = tempnext;
      return retval;
    }

    public string InstantiateFunctionCallExpr(Expression e, Dictionary<string, string> replace = null) {
      FunctionCallExpr exp = (FunctionCallExpr)e;
      string name = exp.Name;
      return InstantiateFunction(name, exp.Args, replace);
    }

    public string InstantiateApplySuffixExpr(Expression e, Dictionary<string, string> replace = null) {
      // don't know the difference between function call expr and apply suffix expression...
      ApplySuffix exp = (ApplySuffix)e;
      string name = ((NameSegment)exp.Lhs).Name;
      return InstantiateFunction(name, exp.Args, replace);
    }

    public string InstantiateNotInExpr(Expression e, Dictionary<string, string> replace = null) {
      BinaryExpr exp = (BinaryExpr)e;
      Debug.Assert(exp.ResolvedOp == BinaryExpr.ResolvedOpcode.NotInSet, "'not in' only supported with sets currently");
      string retval = "(ite (= ";
      retval += InstantiateSetMembership(e, replace);
      retval += " bv_true) bv_false bv_true)";
      return retval;
    }

    public string InstantiateInExpr(Expression e, Dictionary<string, string> replace = null) {
      // use vmt array stuff
      BinaryExpr exp = (BinaryExpr)e;
      Debug.Assert(exp.ResolvedOp == BinaryExpr.ResolvedOpcode.InSet, "'in' only supported with sets currently");
      return InstantiateSetMembership(e, replace);
    }

    public string InstantiateSetMembership(Expression e, Dictionary<string, string> replace = null) {
      BinaryExpr exp = (BinaryExpr)e;
      Expression first = exp.E0;
      Expression second = exp.E1;

      string firsthalf = InstantiateExpr(first, replace);
      string secondhalf = InstantiateExpr(second, replace);
      bool need_next = false;
      if (secondhalf.EndsWith("_next")) {
        secondhalf = secondhalf.Remove(secondhalf.Count() - 5, 5);
        need_next = true;
      }
      if (firsthalf.EndsWith("_next")) {
        firsthalf = firsthalf.Remove(firsthalf.Count() - 5, 5);
        need_next = true;
      }
      string retval = secondhalf + "_" + firsthalf;
      if (need_next) {
        retval += "_next";
      }
      return retval;
    }
    public string InstantiateExprDotNameExpr(Expression e, Dictionary<string, string> replace = null) {
      ExprDotName exp = (ExprDotName)e;
      Expression lhs = exp.Lhs;
      string rhs = exp.SuffixName;
      string retval = "";
      Debug.Assert(lhs is NameSegment, "complex expression for ExprDotName lhs unsupported");
      Debug.Assert(replace != null, "the impossible happened! ExprDotName with no finitization!");
      NameSegment obj = (NameSegment)lhs;

      if (obj.Name == PrevName || obj.Name == NextName) {
        // state machine
        retval += "DafnyState_" + rhs;
        if (obj.Name == NextName) {
          retval += "_next";
        }
      } else {
        retval += replace[obj.Name] + "_" + rhs;
        if (obj.Name.EndsWith("'")) {
          retval += "_next";
        }
      }
      return retval;
    }

    public string InstantiateNameSegment(Expression e, Dictionary<string, string> replace = null) {
      Debug.Assert(replace != null, "the impossible happened! name segment not finite?");
      NameSegment exp = (NameSegment)e;
      if (exp.Name.EndsWith("'")) {
        return replace[exp.Name] + "_next";
      }
      return replace[exp.Name];
    }

  }
}