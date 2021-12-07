using System;
using System.IO;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;
using System.Linq;
using System.Diagnostics;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
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
    private string STATE_MACHINE_INVARIANT_PRED_NAME = "Invariant";
    private string STATE_MACHINE_RELATION_PREFIX = "Relation";
    private string STATE_MACHINE_ACTION_PREFIX = "Action";

    public Dictionary<string, int> Instances;
    public HashSet<int> TypeLengthSet = new HashSet<int> { 0, 1 };

    //public Expression InitExpression;

    public Predicate InitPredicate = null;
    public Predicate NextPredicate = null;
    public Predicate InvariantPredicate = null;

    public string PrevName = null;

    public string NextName = null;

    // maps name of relation to names of datatypes
    public Dictionary<string, List<string>> RelationDatatypeParams = new Dictionary<string, List<string>>();

    public Dictionary<string, List<string>> RelationCombos = new Dictionary<string, List<string>>();

    public List<Predicate> ActionPredicates = new List<Predicate>();

    public VMTPrinter(TextWriter wr,
                      Dictionary<string, int> datatypeInstanceCounts,
                      DafnyOptions.PrintModes printMode = DafnyOptions.PrintModes.Everything)
        : base(wr, printMode) {
      Instances = datatypeInstanceCounts;
    }

    public override void PrintProgram(Program prog, bool afterResolver) {
      Console.WriteLine("Creating finite instance in VMT. Datatype instance counts:");
      Console.WriteLine(Instances);

      wr.Write(VMT_HEADER);

      ParseDatatypes(prog);
      ParsePredicates(prog);
      BuildRelations();
      BuildInit();
      BuildActions();
      DeclareActionsAndTransitionRelations();
      BuildNext();
      BuildInvariant();

      wr.Flush();
    }

    public void ParseDatatypes(Program prog) {  // TODO TODO TODO PARSE CONSTRUCTOR(S)
      wr.WriteLine("\n; Define and enumerate transition system parameters");

      int numFoundFinitizedDatatypes = 0;

      foreach (TopLevelDecl d in prog.DefaultModuleDef.TopLevelDecls) {
        if (d is DatatypeDecl) {
          var dd = (DatatypeDecl)d;
          var name = dd.Name;

          if (name == STATE_MACHINE_DATATYPE_NAME) {
            // Dealing with outer state machine datatype
            continue;
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

            // ParseDatatypeCtors(dd);
          } else {
            Debug.Assert(false, "Datatype '" + name + "' found in Dafny program but no finitization provided on command line.");
          }
        }
      }

      Debug.Assert(numFoundFinitizedDatatypes == Instances.Count, "Command line contains finitized datatype(s) not found in Dafny program.");
    }

    // public void ParseDatatypeCtors(DatatypeDecl dd) {
    //   Debug.Assert(dd.Ctors.Count == 1, "Datatype '" + dd.Name + "' has more than one constructor. This is not currently handled.");

    //   DatatypeCtor ctor = dd.Ctors[0];

    //   var datatypeParams = new List<string>();
    //   foreach (Formal f in pred.Formals) {
    //     string typeName = f.Type.ToString();
    //     if (typeName != STATE_MACHINE_DATATYPE_NAME && !Instances.Keys.Contains(typeName)) {
    //       Debug.Assert(false, "Relation '" + name + "' passed parameter of type '" + typeName + "' not in state machine datatypes");
    //     }
    //     if (typeName != STATE_MACHINE_DATATYPE_NAME) {
    //       datatypeParams.Add(typeName);
    //     }
    //   }
    //   RelationDatatypeParams.Add(name, datatypeParams);
    // }

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
      Debug.Assert(InvariantPredicate != null, "Dafny program is missing the '" + STATE_MACHINE_INVARIANT_PRED_NAME + "' predicate.");
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
      } else if (name == STATE_MACHINE_INVARIANT_PRED_NAME) {
        Debug.Assert(pred.Formals.Count == 1, "Invariant predicate must take exactly one parameter, of type " + STATE_MACHINE_DATATYPE_NAME);
        InvariantPredicate = pred;
      } else if (name.StartsWith(STATE_MACHINE_RELATION_PREFIX) && name != STATE_MACHINE_RELATION_PREFIX) {
        // Dealing with a relation
        var datatypeParams = new List<string>();
        foreach (Formal f in pred.Formals) {
          string typeName = f.Type.ToString();
          if (typeName != STATE_MACHINE_DATATYPE_NAME && !Instances.Keys.Contains(typeName)) {
            Debug.Assert(false, "Relation '" + name + "' passed parameter of type '" + typeName + "' not in state machine datatypes");
          }
          if (typeName != STATE_MACHINE_DATATYPE_NAME) {
            datatypeParams.Add(typeName);
          }
        }
        RelationDatatypeParams.Add(name, datatypeParams);
      } else if (name.StartsWith(STATE_MACHINE_ACTION_PREFIX) && name != STATE_MACHINE_ACTION_PREFIX) {
        // Dealing with an action
        Debug.Assert(pred.Formals.Count == 2
                     && pred.Formals[0].Type.ToString() == STATE_MACHINE_DATATYPE_NAME
                     && pred.Formals[1].Type.ToString() == STATE_MACHINE_DATATYPE_NAME,
                     "Action predicates must take exactly two parameters, of type " + STATE_MACHINE_DATATYPE_NAME
                     + ". The first represents the current/previous state, the second represents the next state.");
        ActionPredicates.Add(pred);
      } else {
        Debug.Assert(false, "Predicate '" + name + "' is not an action, relation, or keyword");
      }
    }

    public void BuildRelations() {
      wr.WriteLine("\n; Declare transition system states");
      foreach (var (relation, datatypeParams) in RelationDatatypeParams) {
        var numDatatypes = datatypeParams.Count;
        var datatypeAmounts = new List<int>(numDatatypes);

        foreach (var datatype in datatypeParams) {
          datatypeAmounts.Add(Instances[datatype]);
        }

        GenRelationCombos(numDatatypes, datatypeAmounts, relation, 0, relation);

        wr.WriteLine("(define-fun update_{0} ((newv {1}_type) (prev {1}_type) (cond Bool) (val {1}_type)) Bool (= newv (ite cond val prev)))",
                     relation, "bool"); // TODO UNHARDCODE BOOL
      }

      foreach (var (key, val) in RelationCombos) {
        foreach (var combo in val) {
          wr.WriteLine("(declare-fun {0} () {1}_type)", combo, "bool"); // TODO TODO TODO UNHARDCODE BOOL
          wr.WriteLine("(declare-fun {0}_next () {1}_type)", combo, "bool"); // TODO TODO TODO UNHARDCODE BOOL
          wr.WriteLine("(define-fun .{0} () {1}_type (! {0} :next {0}_next))", combo, "bool"); // TODO TODO TODO UNHARDCODE BOOL
        }
      }
    }

    public void GenRelationCombos(int numDatatypes, List<int> datatypeAmounts, string str, int currIndex, string relation) {
      if (currIndex == 0 && !RelationCombos.ContainsKey(relation)) {
        RelationCombos.Add(relation, new List<string>());
      }
      if (currIndex == numDatatypes - 1) {
        // Last level, iterate
        for (int lastLevelIter = 0; lastLevelIter < datatypeAmounts[currIndex]; ++lastLevelIter) {
          RelationCombos[relation].Add(str + "_" + RelationDatatypeParams[relation][currIndex] + lastLevelIter);
          // wr.WriteLine("(declare-fun {0} () {1}_type)", finalStr, "bool"); // TODO TODO TODO UNHARDCODE BOOL
          // wr.WriteLine("(declare-fun {0}_next () {1}_type)", finalStr, "bool"); // TODO TODO TODO UNHARDCODE BOOL
          // wr.WriteLine("(define-fun .{0} () {1}_type (! {0} :next {0}_next))", finalStr, "bool"); // TODO TODO TODO UNHARDCODE BOOL
          // Next thing in translate.py for unhardcoding bool:
          // if ret != 'bool_type':
          //   lemmas.append('(is_%s %s)' % (x.sort, name))
        }
      } else {
        for (int intraLevelIter = 0; intraLevelIter < datatypeAmounts[currIndex]; ++intraLevelIter) {
          GenRelationCombos(numDatatypes, datatypeAmounts, str + "_" + RelationDatatypeParams[relation][currIndex] + intraLevelIter, currIndex + 1, relation);
        }
      }
    }

    public void BuildInit() {
      //base.PrintExpression(InitExpression, false);
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
      //base.PrintExpression(InitExpression, false);
      foreach (Predicate pred in ActionPredicates) {
        PrevName = pred.Formals[0].Name;
        NextName = pred.Formals[1].Name;
        // TODO NOT DONE NOT DONE NOT DONE
        wr.Write("(define-fun {0}_fun () Bool (", pred.Name);
        wr.Write("(= ");
        wr.Write(InstantiateExpr(pred.Body));
        wr.Write(" bv_true)");
        wr.Write("))\n");
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
      foreach (var (key, val) in RelationCombos) {
        foreach (var combo in val) {
          checkNoAction += " (= " + combo + " " + combo + "_next)";
        }
      }
      checkNoAction += "))";

      wr.WriteLine("(define-fun .trans () Bool (! (and" + checkActions + checkNoAction + ") :trans true))");
    }

    public void BuildInvariant() {
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
      } else {
        return UnhandledCase(e, replace);
      }

    }
    public string InstantiateBinaryExpr(Expression e, Dictionary<string, string> replace = null) {
      //assert(e is BinaryExpr);
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
      Debug.Assert(exp.Op == BinaryExpr.Opcode.And);
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
      string retval = "";
      if (name.StartsWith(STATE_MACHINE_RELATION_PREFIX)) {
        retval += name;
        if (replace != null) {
          for (int i = 1; i < args.Count; ++i) {
            NameSegment current = (NameSegment)args[i];
            retval += "_" + replace[current.Name];
          }
          NameSegment first = (NameSegment)args[0];
          if (first.Name == NextName) {
            retval += "_next";
          } else if (first.Name != PrevName) {
            Debug.Assert(false, "invalid name for state machine:" + first.Name);
          }
        } else {
          // is this possible?
          Debug.Assert(false, "goofball! the impossible happened!");
        }
      }

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

    public string InstantiateInExpr(Expression e, Dictionary<string, string> replace = null) {
      return UnhandledCase(e, replace);
    }

    public string InstantiateExprDotNameExpr(Expression e, Dictionary<string, string> replace = null) {
      return UnhandledCase(e, replace);
    }


  }

}