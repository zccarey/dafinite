
# Running Dafinite via the Dafny compiler:
Usage:
```
dafny <sourcefile> /finitize:<finitization> /vprint <vmtFile>
```
Pass `-` for `<vprint>` to print to stdout.
Full Example:
```
dafny lock_server.dfy /finitize:Server=1,Client=2 /vprint lock_server_out.vmt
```


# Dafinite Datatypes

- There must be a datatype `DafnyState` that embodies the state. The only parameters it can take are sets of finitized datatypes.
- All other datatypes are the finitized types specified on the command line.    
- Each finitized datatype must have exactly one constructor in the form `datatype NAME = NAME(members)`
- All of the finitized types specified on the command line must appear in the Dafny program.
- If a datatype needs a unique ID, its constructor should take an integer parameter (`id: int`).

# Special Dafinite Expressions

- There must be an `Init` predicate, `Next` predicate, and `Safety` predicate.
    - `Init` must take as a parameter a single instance of `DafnyState` and must return true if and only if the state is a valid initial state.
    - `Next` must take two `DafnyStates` as parameters, corresponding to the previous and new states. It must return true if and only if the system can transition from the previous state to the new state. This must be a disjunction (`||`) of all of the Action predicates (described below).
    - `Safety` must take as a parameter a single instance of `DafnyState`, and must return true if and only if the safety property of the protocol is satisfied.
- State transitions are expressed as predicates with names beginning with `Action`
    - These predicates must take exactly two parameters, both versions of the `DafnyState`, and must return true if and only if the state can transition from the previous to the new state via this action.
- Other predicates are allowed, as long as their parameters are finitizable.

# Other Naming Conventions
All expressions that refer to the next state must end with `'`. For example, for a predicate `pred(m: DafnyState, m': DafnyState)`, the `m'` refers to the next version of `DafnyState`.

# Supported Expressions

Due to time constraints, only a subset of Dafny expressions are supported at the moment. These expressions were chosen because they allowed for implementing real protocols. While this expression list can be expanded in the future, the current supported expressions include:
  - boolean values, `true` and `false`
  - The boolean logic operators `&&`, `||`, `!`, `==>`
  - `==` and `!=` for ID and boolean values (not DATATYPES)
  - Quantifiers `forall` and `exists` on finitized objects
  - Calling predicates on finitized parameters
  - Parenthesis expressions
  - Simple dot expressions (take the form EXPR.EXPR)
    - Allowed: PREFIXNAME.SUFFIXNAME (such as `m.clients`)
    - Not Allowed: COMPLEXEXPR.SUFFIXNAME (such as `m.clients[0].connServers[0].semaphore`)
  - Sets of Finitized objects
  - Set membership: `in` and `!in` on simple expressions
    - Allowed: OBJ in OBJ (such as `c in m.clients`)
    - Not Allowed: COMPLEXEXPR in COMPLEXEXPR
    