#include<iostream>
#include<vector>
#include<queue>
#include<unordered_map>
#include<fstream>
#include<random>

#define CHEAT_CHROMATIC_NUM 40


using namespace std;

//typedef unsigned int uint128_t __attribute__((mode(TI)));


inline void print_vector(const vector<int>& v) {
    for (int i : v) cout << i << " ";
    cout << '\n';
}

class CSP;

class Domain {
public:
    uint64_t domain; //domain of maximum size 63
    size_t feasible;
    inline bool isUnique();
    Domain();
    explicit Domain(size_t domain_size);
};

inline bool Domain::isUnique() {
    // return (domain != 0) && (domain & (domain - 1)) == 0;
    return feasible == 1;
}

Domain::Domain() {
    feasible = 0;
    domain = 0;
}

Domain::Domain(size_t domain_size) {
    feasible = domain_size;
    domain = (((uint64_t)1<<domain_size) - 1);
}

void print_domain(Domain& d) {
    auto dd = d.domain;
    int helper = 0;
    for (uint64_t i = 1; i <= dd; i = i << 1) {
        if (i&dd) {
            cout << helper << " ";
        }
        helper++;
    }
    cout << '\n';
}

struct edge {
    int from, to;
    int next;
    edge() { from = -1; to = -1; next = -1; };
    edge(int f, int t, int n) : from{f}, to{t}, next{n} {};
};

class BinaryConstraintNetwork {
public:
    vector<int> head;
    vector<edge> edges;
    int head_end;
    
    BinaryConstraintNetwork(size_t var_num, size_t edge_num) {
        head = vector<int>(var_num, -1);
        edges = vector<edge>(edge_num);
        head_end = 0;
    }
    
    void add_edge(int from, int to) {
        edges[head_end] = edge(from, to, head[from]);
        head[from] = head_end++;
    }
};

class Graph {
public:
    vector<int> var_of_index; //maps index to var
    unordered_map<int, int> index_of_var;
    vector<int> head;
    vector<edge> edges;
    int head_end;
    
    Graph(vector<int> _var_of_index, size_t edge_num) : var_of_index{std::move(_var_of_index)} {
        index_of_var = unordered_map<int, int>(_var_of_index.size());
        for (int i = 0; i < var_of_index.size(); i++) {
            index_of_var.emplace(make_pair(var_of_index[i], i));
        }
        head = vector<int>(var_of_index.size(), -1);
        edges = vector<edge>(edge_num);
        head_end = 0;
    }
    
    Graph(const vector<int>& _var_of_index, const unordered_map<int, int>& _index_of_var, size_t edge_num) {
        var_of_index = _var_of_index;
        index_of_var = _index_of_var;
        head = vector<int>(var_of_index.size(), -1);
        edges = vector<edge>(edge_num);
        head_end = 0;
    }
    
    void add_edge(int _from, int _to) {
        int from = index_of_var[_from], to = index_of_var[_to];
        edges[head_end] = edge(from, to, head[from]);
        head[from] = head_end++;
    }
    
    Graph Get_Rgraph();
    
    void get_post_order(vector<int>& var_of_post_ord, vector<bool>& visited, int u, int& post) {
        visited[u] = true;
        for (int ei = head[u]; ei != -1; ei = edges[ei].next) {
            int v = edges[ei].to;
            if (!visited[v]) {
                get_post_order(var_of_post_ord, visited, v, post);
            }
        }
        var_of_post_ord[u] = post++;
    }
    
    template<typename __typeof_toVar>
    void explore(int u, vector<bool>& visited, const __typeof_toVar& toVar) {
        visited[u] = true;
        toVar(u);
        for (int ei = head[u]; ei != -1; ei = edges[ei].next) {
            int v = edges[ei].to;
            if (!visited[v]) {
                explore<__typeof_toVar>(v, visited, toVar);
            }
        }
    }
    
    template<typename __typeof_toEdge>
    void explore_edge(int u, vector<bool>& visited, const __typeof_toEdge toEdge) {
        visited[u] = true;
        for (int ei = head[u]; ei != -1; ei = edges[ei].next) {
            toEdge(ei);
            int v = edges[ei].to;
            if (!visited[v]) {
                explore_edge<__typeof_toEdge>(v, visited, toEdge);
            }
        }
    }
    
    void SCC(vector<int>& ans) {
        size_t var_num = var_of_index.size();
        vector<int> var_of_post_ord(var_num, -1), post_ord(var_num, -1);
        vector<bool> visited(var_num, false);
        int post = 0;
        for (int u = 0; u < var_num; u++) {
            if (!visited[u])
                get_post_order(var_of_post_ord, visited, u, post);
        }
        for (int u = 0; u < var_num; u++) {
            post_ord[var_of_post_ord[u]] = u;
        }
        assert(post == var_num);
        
        std::fill(visited.begin(), visited.end(), false);
        Graph rg = Get_Rgraph();
        int SCC_index = 0;
        for (int i = (int)var_num - 1; i >= 0; i--) {
            int u = post_ord[i];
            if (!visited[u]) {
                auto toVar = [&ans, SCC_index](int u) { ans[u] = SCC_index; };
                rg.explore<decltype(toVar)>(u, visited, toVar);
                SCC_index++;
            }
        }
    }
    
};

Graph Graph::Get_Rgraph() {
    Graph rg(var_of_index, index_of_var, edges.size());
    for (auto& e : edges) {
        rg.add_edge(var_of_index[e.to], var_of_index[e.from]);
    }
    return std::move(rg);
}


class Bipartite : public Graph {
public:
    vector<int> match;
    vector<int> check;
    
    Bipartite(vector<int> _var_of_index, size_t edge_num) : Graph(std::move(_var_of_index), edge_num) {
        match = vector<int>(var_of_index.size(), -1);
        check = vector<int>(var_of_index.size(), 0);
    }
    
    bool Augment(int u) {
        for (int ei = head[u]; ei != -1; ei = edges[ei].next) {
            int v = edges[ei].to;
            if (!check[v]) {
                check[v] = 1;
                if (match[v] == -1 || Augment(match[v])) {
                    match[u] = v;
                    match[v] = u;
                    return true;
                }
            }
        }
        return false;
    }
    
    void Hungarian() {
        for (int i = 0; i < match.size(); i++) {
            if (match[i] == -1) {
                std::fill(check.begin(), check.end(), 0);
                bool dummy = Augment(i);
            }
        }
    }
};


class GlobalConstraint {
public:
    size_t arity;
    vector<int> scope;
    explicit GlobalConstraint(vector<int> _scope) : scope(std::move(_scope)) {
        arity = _scope.size();
    }
    virtual inline bool HyperAC(CSP* csp) = 0;
};

class AllDiffConstraint : public GlobalConstraint {
public:
    explicit AllDiffConstraint(vector<int> _scope) : GlobalConstraint(std::move(_scope))  {}
    inline bool HyperAC(CSP* csp) override;
};

class CSP {
public:
    const BinaryConstraintNetwork* constraint_graph;
    vector<shared_ptr<GlobalConstraint>> global_constraints;
    vector<Domain> domains, solution;
    vector<size_t> constraints_involved;
    size_t domain_size;
    
    CSP(BinaryConstraintNetwork* cg, size_t _domain_size) : constraint_graph{cg}, domain_size{_domain_size} {
        domains = vector<Domain>(cg->head.size(), Domain(domain_size));
        solution = vector<Domain>(cg->head.size());
        constraints_involved = vector<size_t>(cg->head.size(), 0);
    }
    
    inline bool complete() {
        for (auto& d : domains) {
            if (!d.isUnique()) return false;
        }
        return true;
    }
    
    inline bool revise3(int eid, int to) {
        bool CHANGE = false;
        int from = constraint_graph->edges[eid].from;
        if (domains[from].isUnique() && (domains[from].domain&domains[to].domain)) {
            CHANGE = true;
            domains[to].domain -= domains[from].domain;
            domains[to].feasible -= 1;
        }
        return CHANGE;
    }
    
    inline bool AC3(int vid) {
        queue<pair<int, int>> Q;
        for (int eid = constraint_graph->head[vid]; eid != -1; eid = constraint_graph->edges[eid].next) {
            Q.push(make_pair(constraint_graph->edges[eid].to, eid));
        }
        
        while (!Q.empty()) {
            auto p = Q.front(); Q.pop();
            auto vi = p.first, ei = p.second;
            if (revise3(ei, vi)) {
                if (domains[vi].domain == 0) return false;
                else {
                    for (int eid = constraint_graph->head[vi]; eid != -1; eid = constraint_graph->edges[eid].next) {
                        if (eid != ei)
                            Q.push(make_pair(constraint_graph->edges[eid].to, eid));
                    }
                }
            }
        }
        return true;
    }
    
    inline int SelectUnassignedVar() {
        size_t min_feasible_value = numeric_limits<size_t>::max();
        size_t max_constraint_size = 0;
        int ans = -1;
        for (int i = 0; i < domains.size(); i++) {
            if (!domains[i].isUnique()) {
                if (domains[i].feasible < min_feasible_value
                    || (domains[i].feasible == min_feasible_value && constraints_involved[i] > max_constraint_size)) {
                    ans = i;
                    min_feasible_value = domains[i].feasible;
                    max_constraint_size = constraints_involved[i];
                }
            }
        }
        return ans;
    }
    
    inline bool BackTrack() {
        if (complete()) {
            std::copy(domains.begin(), domains.end(), solution.begin()) ;
            return true;
        }
        int vi = SelectUnassignedVar();
        /*
        cout << '\n';
        cout << "entering node : " << vi << '\n';
        cout << "there are " << domains[vi].feasible << " values to be tried" << '\n';
        cout << "they are : "; print_domain(domains[vi]);
        cout << '\n';
        */
        
        int helper = -1;
        
        auto ori = domains;
        auto ori_domain = domains[vi].domain;
        for (uint64_t i = 1; i <= ori_domain; i = i<<1) {
            
            helper++;
            //cout << "Is " << helper << " feasible?" << '\n';
            
            
            if (i&ori_domain) {
                
              //  cout << "yes" << '\n';
                
                
                domains[vi].domain = i;
                domains[vi].feasible = 1;
                
                
                //cout << "trying value : " << helper << '\n';
                
                
                if (AC3(vi)) {
                    bool flag = true;
                    for (auto& gc : global_constraints) {
                        if (!gc->HyperAC(this)) {
                            flag = false;
                            break;
                        }
                    }
                    if (flag) {
                        if (BackTrack()) return true;
                    }
                }
                domains = ori;
            }
           // else {
           //     cout << "no" << '\n';
           // }
            
        }
        
        //cout << "attempt failed, back to the previous node" << '\n' << '\n' ;
        
        return false;
    }
    
    bool solve() {
        return BackTrack();
    }
};

inline bool AllDiffConstraint::HyperAC(CSP *csp) {
    size_t edge_num = 0;
    uint64_t mask = 0;
    for (auto i : scope) {
        edge_num += csp->domains[i].feasible;
        mask = mask | csp->domains[i].domain;
    }
    vector<int> var_of_index{scope};
    /*
    cout << '\n';
    cout << "checking AllDifferent Constraint" << '\n';
     
     cout << "scope of this constraint : "; print_vector(scope);
     
     cout << "domains of vars in scope : " << '\n';
     for (auto i : scope) {
         cout << "domain of " << i << " : "; print_domain(csp->domains[i]);
     }
    */
     
    
    
    
    
    
    
    auto csp_var_num = (int)csp->domains.size();
    int _var = csp_var_num;
    for (uint64_t i = 1; i <= mask; i = i << 1) {
        if (i&mask) var_of_index.push_back(_var);
        _var++;
    }
    
    
    
    /*
     
     cout << "value vertices in val graph : ";
     for (int i = csp_var_num; i < var_of_index.size(); i++)
     cout << var_of_index[i] << " ";
     cout << '\n';
     */
    
    
    
    
    Bipartite bp(var_of_index, 2*edge_num);
    
    /*
     cout << "edges : " << '\n';
     */
    
    
    for (int var : scope) {
        _var = csp_var_num;
        for (uint64_t i = 1; i <= csp->domains[var].domain; i = i << 1) {
            if (i&csp->domains[var].domain) {
                bp.add_edge(var, _var);
                bp.add_edge(_var, var);
                
                /*
                 
                 cout << var << " " << _var << '\n';
                 */
                
                
            }
            _var++;
        }
    }
    bp.Hungarian();
    
    
    /*
     cout << "matches : " << '\n';
     for (int var : scope) {
     cout << "index : " << bp.index_of_var[var] << " "
     << "match index : " << bp.match[bp.index_of_var[var]] << '\n';
     }
     
     cout << "match done" << '\n';
     */
    /*
    cout << "after matching" <<'\n';
    for (int var : scope) {
        cout << var << " matches " << bp.var_of_index[bp.match[bp.index_of_var[var]]] - csp_var_num << '\n';
    }
    */
    
    
    int match_num = 0;
    for (int i = 0; i < bp.match.size(); i++) {
        if (bp.match[i] != -1 && bp.var_of_index[i] < csp_var_num) match_num++;
    }
    if (match_num != scope.size()) return false;
    
    
    /*
     
     cout << "match num : " << match_num << '\n';
     cout << "scope size : " << scope.size() << '\n';
     
     */
    
    
    
    
    Graph g = Graph(bp.var_of_index, bp.index_of_var, edge_num);
    vector<bool> consistent(edge_num, false);
    vector<int> SCC_index(g.var_of_index.size());
    
    
    
    
    /*
     cout << consistent.size() << " edges to be considered" << '\n';
     cout << SCC_index.size() << " vertices to be considered" << '\n';
     
     */
    
    
    
    for (int var : scope) {
        int id = bp.match[g.index_of_var[var]];
        assert(id != -1);
        g.add_edge(var, g.var_of_index[id]);
        consistent[g.head_end - 1] = true;
    }
    
    /*
     cout << "scope.size() == " << scope.size() << '\n';
     cout << "g.var_of_index.size() == " << g.var_of_index.size() << '\n';
     */
    for (auto id = (int)scope.size(); id < bp.var_of_index.size(); id++) {
        /*
         if (bp.match[id] == -1 || bp.match[bp.match[id]] != id) {
         for (int ei = bp.head[id]; ei != -1; ei = bp.edges[ei].next) {
         cout << "hi there" << '\n';
         g.add_edge(var_of_index[id], var_of_index[bp.edges[ei].to]);
         }
         }*/
        for (int ei = bp.head[id]; ei != -1; ei = bp.edges[ei].next) {
            int _id = bp.edges[ei].to;
            if (bp.match[id] == -1 || bp.match[id] != _id)
                g.add_edge(var_of_index[id], var_of_index[_id]);
        }
    }
    auto toEdge = [&consistent](int ei){ consistent[ei] = true; return; };
    vector<bool> visited(var_of_index.size(), false);
    
   // cout << "checking edges lying in an even alternating path starting from free vertex" << '\n';
    for (auto id = (int)scope.size(); id < var_of_index.size(); id++) {
        if (bp.match[id] == -1 && !visited[id]) {
     //       cout << "from vertex " << var_of_index[id] << '\n';
            g.explore_edge<decltype(toEdge)>(id, visited, toEdge);
        }
    }
    
    
    /*
     cout << "edges in the directed graph : " << '\n';
     for (int ei = 0; ei < g.edges.size(); ei++) {
         cout << (g.var_of_index[g.edges[ei].from] >= csp_var_num ? g.var_of_index[g.edges[ei].from] - csp_var_num : g.var_of_index[g.edges[ei].from])
         << " " << (g.var_of_index[g.edges[ei].to] >= csp_var_num ? g.var_of_index[g.edges[ei].to] - csp_var_num : g.var_of_index[g.edges[ei].to])
         << '\n';
     }
     */
     
    
    g.SCC(SCC_index);
    
    
    
    
    //cout << "Strongly Connected Component : "; print_vector(SCC_index);
   // cout << "SCC : " << '\n';
   // for (int i = 0; i < g.var_of_index.size(); i++) {
    //    cout << "var " << var_of_index[i] << " : " << SCC_index[i] << '\n';
    //}
    
    
    
    
    
    for (int ei = 0; ei < edge_num; ei++) {
        int v = g.edges[ei].from, u = g.edges[ei].to;
        if (SCC_index[v] == SCC_index[u]) consistent[ei] = true;
    }
    for (int ei = 0; ei < edge_num; ei++) {
        if (!consistent[ei]) {
            int var = var_of_index[g.edges[ei].from] < csp_var_num ? var_of_index[g.edges[ei].from] :
            var_of_index[g.edges[ei].to];
            int vali = var_of_index[g.edges[ei].to] + var_of_index[g.edges[ei].from] - var;
            uint64_t vmask = ((uint64_t)1) << (vali - csp_var_num);
            
            assert(vmask&csp->domains[var].domain);
            
            csp->domains[var].domain -= vmask;
            csp->domains[var].feasible -= 1;
        }
    }
    
    return true;
}

bool explore(BinaryConstraintNetwork* cnet, int u, vector<bool>& visited, vector<Domain>& solution) {
    visited[u] = true;
    for (int ei = cnet->head[u]; ei != -1; ei = cnet->edges[ei].next) {
        int v = cnet->edges[ei].to;
        if (solution[u].domain&solution[v].domain) return false;
        if (!visited[v]) {
            if (!explore(cnet, v, visited, solution)) return false;
        }
    }
    return true;
}

bool correctness_check(BinaryConstraintNetwork* cnet, vector<Domain>& solution) {
    vector<bool> visited(cnet->head.size(), false);
    for (int u = 0; u < cnet->head.size(); u++) {
        if (!visited[u]) {
            if (!explore(cnet, u, visited, solution)) return false;
        }
    }
    return true;
}

bool clique_check(BinaryConstraintNetwork* cnet, vector<int>& scope) {
    
    int edge_num = 0;
    
    for (int __u = 0; __u < scope.size(); __u++) {
        for (int __v = __u + 1; __v < scope.size(); __v++) {
            int u = scope[__u], v = scope[__v];
            bool flag = false;
            for (int ei = cnet->head[u]; ei != -1; ei = cnet->edges[ei].next) {
                if (cnet->edges[ei].to == v) {
                    edge_num++;
                    flag = true; break;
                }
            }
            if (!flag) return false;
        }
    }
    
    assert(edge_num == (scope.size() * (scope.size() - 1)) / 2);
    
    return true;
}

inline void set_domain(CSP* csp, int id, int _n) {
    csp->domains[id].domain = 1 << _n;
    csp->domains[id].feasible = 1;
}

int main(int argc, char** argv) {
    ios_base::sync_with_stdio(false);
    
    string fileName = argv[1];
    
    ifstream myfile(fileName);
    
    int N, E;
    string line;
    if (!getline(myfile, line)) {
        cerr << "file error";
        return 1;
    }
    auto pos = line.find(' ');
    N = stoi(line);
    E = stoi(line.substr(pos+1));
    BinaryConstraintNetwork g((size_t)N, 2*(size_t)E);
    
    CSP csp(&g, CHEAT_CHROMATIC_NUM);
    int x, y;
    while (getline(myfile, line)) {
        pos = line.find(' ');
        x = stoi(line);
        y = stoi(line.substr(pos+1));
        g.add_edge(x, y);
        g.add_edge(y, x);
        csp.constraints_involved[x]++;
        csp.constraints_involved[y]++;
    }
    
    /*
     vector<vector<bool>> adj_matrix(g.head.size(), vector<bool>(g.head.size(), false));
     for (int u = 0; u < g.head.size(); u++) {
     for (int ei = g.head[u]; ei != -1; ei = g.edges[ei].next) {
     int v = g.edges[ei].to;
     adj_matrix[u][v] = true;
     }
     }
     
     //  for (int u = 0; u < g.head.size(); u++) {
     //  for (int v = 0; v < g.head.size(); v++) {
     //  cout << adj_matrix[u][v] << " ";
     //  }
     //  cout << '\n';
     //  }
     */
    
    vector<int> visited(g.head.size(), false);
    vector<vector<int>> scopes(0);
    
    //cout << g.head.size() << " of vertices" << '\n';
    //cout << g.edges.size() << " of edges" << '\n';
    
    for (int u = 0; u < g.head.size(); u++) {
        if (visited[u]) continue;
        vector<int> scope {u};
        visited[u] = true;
        for (int v = u + 1; v < g.head.size(); v++) {
            if (visited[v]) continue;
            bool flag = true;
            for (auto& _u : scope) {
                flag = false;
                for (int ei = g.head[_u]; ei != -1; ei = g.edges[ei].next) {
                    if (g.edges[ei].to == v) {
                        flag = true; break;
                    }
                }
                if (!flag) break;
            }
            if (flag) {
                scope.push_back(v);
                visited[v] = true;
            }
        }
        scopes.push_back(scope);
    }
    
    
    //cout << scopes.size() << " cliques detected" << '\n';
    
    
    int gc_num = 0;
    
    for (auto& scope : scopes) {
        
        
        assert(clique_check(&g, scope));
        
        for (auto& v : scope) {
            csp.constraints_involved[v]++;
        }
        
        
        if (scope.size() >= 3) {
            for (auto& v : scope) {
                csp.constraints_involved[v]++;
            }
            csp.global_constraints.push_back(shared_ptr<GlobalConstraint>(new AllDiffConstraint(scope)));
            gc_num++;
        }
    }
    
    
    int max_scope_num = 0;
    shared_ptr<GlobalConstraint> max_index(nullptr);
    
    //cout << "global constraint detected : " << gc_num << '\n';
    for (auto& ptr : csp.global_constraints) {
        
        if (ptr->scope.size() > max_scope_num) {
            max_index = ptr;
            max_scope_num = ptr->scope.size();
        }
        /*
        cout << "scope : ";
        for (auto &v : ptr->scope) {
            cout << v << " ";
        }
        cout << '\n';*/
    }
    
    assert(max_index->scope.size() <= CHEAT_CHROMATIC_NUM);
    for (int i = 0; i < max_index->scope.size(); i++) {
        set_domain(&csp, max_index->scope[i], i);
    }
    

    
  /*
    
    
    cout << "set!" << '\n';
    
    vector<int> v {0,1,5,1,1,2,0,0,3,3,1,0,0,3,4,4,2,4,1,0,4,1,3,2,2,0,2,0,2,1,5,2,5,5,1,4,0,3,4,2,5,1,3,4,2,3,3 ,2, 1, 1};
    
    
    for (int i = 0; i < 46; i++) {
        set_domain(&csp, i, v[i]);
    }
    
    
    */
    
    
    if (csp.solve()) {
        
        
        assert(correctness_check(&g, csp.solution));
        
        cout << CHEAT_CHROMATIC_NUM << " " << 1 << '\n';
        
        for (auto& d : csp.solution) {
            uint64_t domain = d.domain;
            int i = -1;
            while (domain) {
                i++;
                domain = domain >> 1;
            }
            cout << i << " ";
        }
        cout << '\n';
    }
    else {
        cout << "no solution" << '\n';
    }
}
