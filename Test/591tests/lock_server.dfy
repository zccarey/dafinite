datatype Server = Server(id:int, semaphore:bool)
datatype Client = Client(id:int, connServers:set<int>)
datatype DafnyState = DafnyState(clients:seq<Client>, servers:seq<Server>)

predicate RelationLink(m: DafnyState, c: Client, s: Server)
{
    && 0 <= s.id < |m.servers|
    && 0 <= c.id < |m.clients|
    && m.servers[s.id].id in m.clients[c.id].connServers
}

predicate RelationSemaphore(m: DafnyState, s: Server)
{
    && 0 <= s.id < |m.servers|
    && m.servers[s.id].semaphore
}

predicate RelationServerExists(m: DafnyState, s: Server){
    s in m.servers
}

predicate RelationClientExists(m: DafnyState, c: Client){
    c in m.clients
}

predicate RelationDifferentClients(m: DafnyState, c1: Client, c2: Client){
    && RelationClientExists(m, c1)
    && RelationClientExists(m, c2)
    && c1.id != c2.id
}

predicate RelationDifferentServers(m: DafnyState, s1: Server, s2: Server){
    && RelationServerExists(m, s1)
    && RelationServerExists(m, s2)
    && s1.id != s2.id
}

predicate Init(m: DafnyState) {
    && (forall s: Server :: RelationServerExists(m, s) ==> RelationSemaphore(m, s))
    && (forall s: Server, c: Client :: ((RelationServerExists(m, s) && RelationClientExists(m, c)) ==> !RelationLink(m, c, s)))
}

predicate ActionConnect(m: DafnyState, m': DafnyState) {
    exists c: Client, s: Server ::

        && RelationSemaphore(m, s) // in original state
        && RelationLink(m', c, s)
        && !RelationSemaphore(m', s)

        && (forall cf: Client, sf: Server :: (RelationDifferentClients(m, cf, c) ==> RelationLink(m, cf, sf) == RelationLink(m', cf, sf)))
        
        && (forall sf: Server :: (RelationDifferentServers(m, sf, s) ==> RelationSemaphore(m, sf) == RelationSemaphore(m', sf)))
}

predicate ActionDisconnect(m: DafnyState, m': DafnyState) {
    exists c: Client, s: Server ::

        && !RelationSemaphore(m, s) // in original state
        && !RelationLink(m', c, s)
        && RelationSemaphore(m', s)

        && (forall cf: Client, sf: Server :: (RelationDifferentClients(m, cf, c) ==> RelationLink(m, cf, sf) == RelationLink(m', cf, sf)))
        
        && (forall sf: Server :: (RelationDifferentServers(m, sf, s) ==> RelationSemaphore(m, sf) == RelationSemaphore(m', sf)))

}

predicate Next(m:DafnyState, m':DafnyState) {
    || ActionConnect(m, m')
    || ActionDisconnect(m, m')
}


predicate Invariant(m: DafnyState)
{
    forall c1: Client, c2:Client, s: Server :: (RelationClientExists(m, c1) && RelationClientExists(m, c2) && RelationServerExists(m, s)) ==> (RelationLink(m, c1, s) && RelationLink(m, c2, s) ==> !RelationDifferentClients(m, c1, c2))
}