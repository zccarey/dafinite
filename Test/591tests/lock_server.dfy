// type client
// type server
datatype Server = Server(semaphore:bool)
datatype Client = Client(connServers:set<Server>)
datatype Machine = Machine(clients:set<Client>, servers:set<Server>)

// relation link(X:client, Y:server)
// relation semaphore(X:server)

// after init {
//     semaphore(W) := true;
//     link(X,Y) := false
// }
predicate Init(m: Machine) {
    (forall s:Server :: s in m.servers ==> s.semaphore == true)
    && (forall c:Client :: c in m.clients ==> |c.connServers| == 0)
}

// action connect(x:client,y:server) = {
//   require semaphore(y);
//   link(x,y) := true;
//   semaphore(y) := false
// }
predicate Connect(m: Machine, m': Machine, c: Client, s: Server) {
    exists c:Client, c':Client, s:Server, s':Server ::
        c in m.clients &&
        c' in m'.clients &&
        s in m.servers &&
        s' in m'.servers &&

        s.semaphore == true &&
        s'.semaphore == false &&
        s' in c'.connServers &&
        forall testC:Client :: testC in m'.clients && s' in testC.connServers ==> testC == c'

    c in m.clients &&
    s in m.servers &&

}

// action disconnect(x:client,y:server) = {
//   require link(x,y);
//   link(x,y) := false;
//   semaphore(y) := true
// }
predicate Disconnect(m: Machine, m': Machine) {
    exists c:Client, c':Client, s:Server, s':Server ::
        c in m.clients &&
        c' in m'.clients &&
        s in m.servers &&
        s' in m'.servers &&

        s.semaphore == false &&
        s'.semaphore == true &&
        forall testC:Client :: testC in m'.clients ==> s' !in testC.connServers
}

predicate Next(m:Machine, m':Machine) {
    || (exists c:Client, s:Server :: Connect(m, m', c, s))
    || (exists c:Client, s:Server :: Disconnect(m, m', c, s))
}

// export connect
// export disconnect

// invariant [1000000] link(C1, S) & link(C2, S) -> C1 = C2
