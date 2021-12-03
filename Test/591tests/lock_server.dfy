// type client
// type server
datatype Server = Server(id:int, semaphore:bool)
datatype Client = Client(id:int, connServers:set<int>)
datatype DafnyStateMachine = DafnyStateMachine(clients:set<Client>, servers:set<Server>)

// relation link(X:client, Y:server)
// relation semaphore(X:server)

// after init {
//     semaphore(W) := true;
//     link(X,Y) := false
// }
predicate Init(m: DafnyStateMachine) {
    (forall s:Server :: s in m.servers ==> s.semaphore == true)
    && (forall c:Client :: c in m.clients ==> |c.connServers| == 0)
}

// action connect(x:client,y:server) = {
//   require semaphore(y);
//   link(x,y) := true;
//   semaphore(y) := false
// }
predicate Connect(m: DafnyStateMachine, m': DafnyStateMachine, c: Client, s: Server) {
    && c in m.clients // client exists
    && s in m.servers // server exists
    && s.semaphore == true // server is unlocked to start
    && Client(c.id, c.connServers + {s.id}) in m'.clients // client ends up locked on this server
    && Server(s.id, false) in m'.servers // server ends up locked
    && (m.servers - {s}) == (m'.servers - {Server(s.id, false)}) // no other changes
    && (m.clients - {c}) == (m'.clients - {Client(c.id, c.connServers + {s.id})}) // no other changes
}

// action disconnect(x:client,y:server) = {
//   require link(x,y);
//   link(x,y) := false;
//   semaphore(y) := true
// }
predicate Disconnect(m: DafnyStateMachine, m': DafnyStateMachine, c: Client, s: Server) {
    && c in m.clients // client exists
    && s in m.servers // server exists
    && s.id in c.connServers // client held server lock
    && Client(c.id, c.connServers - {s.id}) in m'.clients // client ends up unlocked on this server
    && Server(s.id, true) in m'.servers // server ends up unlocked
    && (m.servers - {s}) == (m'.servers - {Server(s.id, true)}) // no other changes
    && (m.clients - {c}) == (m'.clients - {Client(c.id, c.connServers - {s.id})}) // no other changes
}

predicate Next(m:DafnyStateMachine, m':DafnyStateMachine) {
    || (exists c:Client, s:Server :: Connect(m, m', c, s))
    || (exists c:Client, s:Server :: Disconnect(m, m', c, s))
}

// export connect
// export disconnect

// invariant [1000000] link(C1, S) & link(C2, S) -> C1 = C2
