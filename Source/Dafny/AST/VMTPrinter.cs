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

    private string STATE_MACHINE_DATATYPE_NAME = "DafnyStateMachine";
    private string STATE_MACHINE_INIT_PRED_NAME = "Init";
    private string STATE_MACHINE_NEXT_PRED_NAME = "Pred";

    public Dictionary<System.Type, Func<Expression, string>> AstDict = new Dictionary<System.Type, Func<Expression, string>>();

    public Dictionary<string, int> Instances;
    public HashSet<int> TypeLengthSet = new HashSet<int> { 0, 1 };

    public VMTPrinter(TextWriter wr,
                      Dictionary<string, int> datatypeInstanceCounts,
                      DafnyOptions.PrintModes printMode = DafnyOptions.PrintModes.Everything)
        : base(wr, printMode) {
      AstDict[typeof(BinaryExpr)] = InstantiateBinaryExpr;
      Instances = datatypeInstanceCounts;
    }

    public override void PrintProgram(Program prog, bool afterResolver) {
      Console.WriteLine("Creating finite instance in VMT. Datatype instance counts:");
      Console.WriteLine(Instances);

      wr.Write(VMT_HEADER);

      ParseDatatypes(prog);
      ParsePredicates(prog);
    }

    public void ParseDatatypes(Program prog) {
      Console.WriteLine("DATATYPES");

      foreach (TopLevelDecl d in prog.DefaultModuleDef.TopLevelDecls) {
        if (d is DatatypeDecl) {
          Console.WriteLine("DATATYPE");
          var dd = (DatatypeDecl)d;
          var name = dd.Name;

          if (name == STATE_MACHINE_DATATYPE_NAME) {
            // Dealing with outer state machine datatype
          } else if (Instances.ContainsKey(name)) {
            // Dealing with one of our finitized datatypes

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
          } else {
            Debug.Assert(false, "Finitized datatype '" + name + "' provided on command line but not found in Dafny program");
          }
          // PrintDatatype(dd, 0, Path.GetFullPath(prog.FullName));
        }
      }

      Console.WriteLine("END DATATYPES");
    }

    public void ParsePredicates(Program prog) {
      Console.WriteLine("PREDICATES");

      foreach (TopLevelDecl d in prog.DefaultModuleDef.TopLevelDecls) {
        if (d is ClassDecl) {
          ClassDecl cl = (ClassDecl)d;
          foreach (MemberDecl mem in cl.Members) {
            if (mem is Function) {
              Function f = (Function)mem;
              if (f is Predicate) {
                Console.WriteLine("PREDICATE");

                ParsePredicate((Predicate)f);

                // PrintFunction(f, 0, false);
              }
            }
          }
        }
      }

      Console.WriteLine("END PREDICATES");
    }

    public void ParsePredicate(Predicate pred) {
      var name = pred.Name;

      if (name == STATE_MACHINE_INIT_PRED_NAME) {
        // Dealing with Init
      } else if (name == STATE_MACHINE_NEXT_PRED_NAME) {
        // Dealing with Next
      } else {
        // Dealing with a state transition
      }
    }

    public string InstantiateBinaryExpr(Expression e) {
      //assert(e is BinaryExpr);
      Debug.Assert(e is BinaryExpr);
      var exp = (BinaryExpr)e;
      switch (exp.Op) {
        case BinaryExpr.Opcode.And:
          return InstantiateAnd(e);
        case BinaryExpr.Opcode.Or:
          return InstantiateOr(e);
        case BinaryExpr.Opcode.Iff:
          return InstantiateImplies(e);
        case BinaryExpr.Opcode.Eq:
          return InstantiateEqual(e);
        case BinaryExpr.Opcode.Neq:
          return InstantiateNotEqual(e);
        default:
          Console.WriteLine("unsupported binary expression: " + exp.Op);
          break;
      }
      return "";
    }

    public string InstantiateAnd(Expression e) {
      BinaryExpr exp = (BinaryExpr)e;
      Debug.Assert(exp.Op == BinaryExpr.Opcode.And);
      string retval = "(ite (and ";
      retval += "(= ";
      retval += AstDict[typeof(Expression)](exp.E0);
      retval += " bv_true) (= ";
      retval += AstDict[typeof(Expression)](exp.E1);
      retval += " bv_true)) bv_true bv_false)";
      return retval;
    }

    public string InstantiateOr(Expression e) {
      BinaryExpr exp = (BinaryExpr)e;
      Debug.Assert(exp.Op == BinaryExpr.Opcode.And);
      string retval = "(ite (or (= ";
      retval += AstDict[typeof(Expression)](exp.E0);
      retval += " bv_true) (= ";
      retval += AstDict[typeof(Expression)](exp.E1);
      retval += " bv_true)) bv_true bv_false)";
      return retval;
    }

    public string InstantiateImplies(Expression e) {
      BinaryExpr exp = (BinaryExpr)e;
      Debug.Assert(exp.Op == BinaryExpr.Opcode.Iff);
      string retval = "(ite (=> (= ";
      retval += AstDict[typeof(Expression)](exp.E0);
      retval += " bv_true) (= ";
      retval += AstDict[typeof(Expression)](exp.E1);
      retval += " bv_true)) bv_true bv_false)";
      return retval;
    }

    public string InstantiateEqual(Expression e) {
      BinaryExpr exp = (BinaryExpr)e;
      Debug.Assert(exp.Op == BinaryExpr.Opcode.Eq);
      string retval = "(ite (= ";
      retval += AstDict[typeof(Expression)](exp.E0);
      retval += " ";
      retval += AstDict[typeof(Expression)](exp.E1);
      retval += ") bv_true bv_false)";
      return retval;
    }

    public string InstantiateNotEqual(Expression e) {
      BinaryExpr exp = (BinaryExpr)e;
      Debug.Assert(exp.Op == BinaryExpr.Opcode.Neq);
      string retval = "(ite (= ";
      retval += AstDict[typeof(Expression)](exp.E0);
      retval += " ";
      retval += AstDict[typeof(Expression)](exp.E1);
      retval += ") bv_false bv_true)";
      return retval;
    }
  }

}