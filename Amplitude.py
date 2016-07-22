from numpy import *
import copy
import re
import sympy
import time
import networkx as nx
import matplotlib.pyplot as plt
from sympy.parsing.sympy_parser import parse_expr


def bits1(n,l=0):
    #takes a binary number n and a length l ; retruns a numpy array of length l with ones for digits of n which are 1
    b = zeros(l,dtype=bool)
    count=0
    while n:
        b[count] = n & 1
        n >>= 1
        count+=1
    return (b)


def Wedge(A,B,n):
    #takes two lists of binary numbers and returns their wedge products mod 2 ( 10101^00010 = 10111 , 100101^100000=000000 2*100110 = 0 ...)
    dic={}
    lis=set()
    for y in A:
        for z in B:
            
            if y^z==y|z:
                if y^z in dic: dic[y^z] = not dic[y^z]
                else :dic[y^z]=True
    return [x for x in dic if dic[x]]

def Wedge_list(L,n):
    #takes a list of binary numbers and return wedge product of all of them
    length =len(L)
    if length==0:return []
    if length==1: return L[0]
    return Wedge(Wedge_list(L[:1],n),Wedge_list(L[1:],n),n)
    
    
class node:
    #Represent a node of graph, each node has an index and a neighborhood 
    def __init__(self,ind=-1,nh=[]):
        self.nh=nh
        self.ind=ind



class graph:
    #contains two dictionaries for edges and nodes(vertices); two dictionary for masses of edges and a momenta of vertics; a dictionary for coefficients of second and first Symanzik polynomials;
    #integer counter for number of edges
    # graph(n=6) construct a graph with 6 vertices labeled 0 to 5 and no edges
    def __init__(self,ver={},n=0,counter=0,edge={},mass={},momentum={},coef={}):
        self.ver={}
        self.coef={}
        self.edge={}
        self.counter=0
        self.mass=mass
        self.momentum=momentum
        for a in range(n):
            temp= node()
            temp.ind=a
            self.ver[a]=temp
            
        
            
    def add_ver(self,v):
        # add a vertex with index v
        self.ver[v]=node()
        self.ver[v].ind=v
        return self
   
    def connect(self,a,b,x=None):
        # add an edge from a to b ( undirected) if x is given set the edge index to x otherwise max number of other edges+1
        # an edge in dictionary self.edge has index as the key and its value is a tuple (a,b); the edge connects a to b where a<=b
        if x==None:x=max(list(self.edge)+[-1])+1
        if a not in self.ver: print("%d is not a vertex"%a);return None
        if b not in self.ver: print("%d is not a vertex"%b);return None
        D=self.ver
        D[a].nh=D[a].nh+[(b,x)]
        D[b].nh=D[b].nh+[(a,x)]
        if a <= b :self.edge[x]=(a,b)
        if a > b :self.edge[x]=(b,a)
        self.counter+=1
        
    def remove_edge(self,e,cop=True):
        #removes an edge index=e; if cop is True return a copy ; otherwise changes the original graph
        if cop==False:
            end= self.ver[self.edge[e][0]]
            start=self.ver[self.edge[e][1]]
            end.nh.remove((start.ind,e))
            start.nh.remove((end.ind,e))
            self.edge.pop(e)
            self.counter-=1
            return self
            
        A=copy.deepcopy(self)
        end= self.edge[e][0]
        
        start=self.edge[e][1]
        
        end=A.ver[end]
        start=A.ver[start]
        end.nh.remove((start.ind,e))
        start.nh.remove((end.ind,e))
        A.edge.pop(e)
        A.counter-=1
        return A
        
    def remove_ver(self,n,cop=True):
        #removes a vertex index=n; if cop is True return a copy ; otherwise changes the original graph
        if cop==False:
            for x in self.ver[n].nh:
                self.ver[x[0]].nh=[y for y in self.ver[x[0]].nh if y[0]!=n]
                self.edge.pop(x[1])
            self.ver.pop(n)
            return self


        
        A=copy.deepcopy(self)
        for x in A.ver[n].nh:
            A.ver[x[0]].nh=[y for y in A.ver[x[0]].nh if y[0]!=n]
            A.edge.pop(x[1])
        A.ver.pop(n)
        return A




    def is_leaf(self,x):
        #checks if edge with index x is a leaf
        start=self.ver[self.edge[x][0]]
        end=self.ver[self.edge[x][1]]
        
        if len(start.nh)==1 or len(end.nh)==1:
            return True
        else : return False
    def has_leaf(self):
        #checks if a graph has a leaf
        for x in self.edge:
            if self.is_leaf(x): return True
        return False

    def to_graph(self,sub):
        # takes a list of edges an constructs the minimal subgraph containing all of them
        A=graph()
        
        for x in sub:
            if self.edge[x][0] not in A.ver : A.add_ver(self.edge[x][0])
            if self.edge[x][1] not in A.ver: A.add_ver(self.edge[x][1])
            A.connect(self.edge[x][0],self.edge[x][1],x)
        return A

    def has_loop(self):
        #checks if the graph has a cycle
        start=next(iter(self.ver))
        stack=[start]
        visited=set()
        while stack:
            vertex=stack.pop()
            if vertex in visited:return True
            else:
                visited.add(vertex)
                nh=(self.ver[vertex].nh)
                nh1=([x[0] for x in nh ])
                nh=set(nh1)
                if len(nh)!=len(nh1):return True
                stack.extend(nh-visited)
        return False
    def cycle(self):
        # returns a cycle as a graph object with the same indexing of the edges and vertices
        for a in self.edge:
            if self.edge[a][0]==self.edge[a][1]:
                result= graph()
                result.add_ver(self.edge[a][0])
                result.connect(self.edge[a][0],self.edge[a][0],x=a)
                return result
        start=list(self.ver.keys())[0]
        
        
        stack=list(self.ver[start].nh)
        visited=set([start])
        path=[]
        T=False
        vertex=0
        while stack:
            
            vertex=stack.pop()
            
            if vertex[0] in visited:T=True; break 
            else:
                
                visited.add(vertex[0])
                path=path+[vertex[1]]
                nh1=(self.ver[vertex[0]].nh)
                nh=set(nh1)
                if len(nh)!=len(nh1):return None
                stack.extend([x for x in nh1 if x[0] not in visited])
                
        
        if not T: return graph()
        
        grap=self.to_graph(path+[vertex[1]])
        b=True
        while b:
            b=False
            for x in list(grap.ver):
                if len(grap.ver[x].nh)==1: grap.remove_ver(x,cop=False);b=True
        return grap    
    def cycles(self):
        #returns a basis for space of cycles( First Homology of the graph)
        A=copy.deepcopy(self)
        temp=[]
        while A.has_loop():
            
            cyc=A.cycle()
            temp.append(cyc)
            A.remove_edge(next(iter(cyc.edge.keys())),cop=False)
        return temp
    
    def np_cycles(self):
        #returns a numpy binary array where each row represent a cycles; True for edges in the cycle and False for other edges
        A=self.cycles()
        B=[list(z.edge.keys()) for z in A]
        
        result=[]
        for x in B:
            temp=zeros((len(x),len(self.edge)),dtype=bool)
            for y in range(len(x)):
                temp[y,x[y]]=True
           
            result.append(temp)
        
        
        return result
    def binary_cycles(self):
        #same as np_cycles but as binary number; in binary expansion 1 represent an edge in cycle and 0 for other edges
        A=self.cycles()
        B=[list(z.edge.keys()) for z in A]
        
        result=[]
        for x in B:
            temp=zeros(len(x),dtype=int64)
            for y in range(len(x)):
                temp[y]=2**x[y]
           
            result.append(temp)
        
        
        return result
    def binary_sp(self):
        # returns a list of binary number; each number represent complement of spanning tree as a binary number
        A=self.binary_cycles()
        n=len(self.edge)
        result= Wedge_list(A,n)
        if len(result)==0:
            return [0]
        return result
        
        
    def connected(self):
        #checks if the graph is connected using DFS
        start=next(iter(self.ver))
        stack=[start]
        visited=set()
        while stack:
            vertex=stack.pop()
            if vertex not in visited:
                visited.add(vertex)
                nh=(self.ver[vertex].nh)
                nh1=([x[0] for x in nh ])
                nh=set(nh1)
                stack.extend(nh-visited)
        if len(visited)==len(self.ver) :return True
        return False   
        

    def is_cover(self,sub):
        #checks if list of edges cover all vertices
        temp=set([])
        for e in sub:
            temp.add(self.edge[e][0])
            temp.add(self.edge[e][1])
        for x in self.ver:
            if x not in temp:
                return False
        return True




    def nh(self,sub):
        # returns all the edges in graph connecting vertices in graph constructed from the list sub to its complement
        if sub==set():
            
            nh=self.edge.keys()
            return set(nh)
            

            
        ver=[self.edge[x][0] for x in sub]
        ver+=[self.edge[x][1] for x in sub]
        ver=set(ver)
        nh=set([])
        for a in ver:
            for b in self.ver[a].nh:
                nh.add(b[1])
        return nh-set(sub)
    
    def dyn_nh(self,nh,edge,end):
        #takes a nh of subgraph and a new edge(edge) with its ending point(end) and returns neighborhood of sub union edge
        
        new=set([x[1]for x in self.ver[end].nh])
        return (new|nh)-set([edge])

    def algo(self,sub,nh,ver):
        # takes a connected sub with its nh a vertices in it and return all subgraph containing it which are connected; neglect some of subgraphs which have leaves
        
        A=self
        result=[]
        temp=[]
        
        for x in set(nh):
            
            new_sub=set(sub)
            new_sub.add(x)
            ends= set(A.edge[x])
            temp=temp+[(x,A.edge[x])]
            T=False
            if len(nh)==0: return []
            for e in ends:
                if e not in ver: T=True;end=e
            if not T:
                result=result+[(new_sub,ver)]
                new_ver=set(ver)
                new_nh=set(nh)-set([x])
                P=A.algo(new_sub,new_nh,new_ver)
                result=result+ P
                A.remove_edge(x,cop=False)
                nh.remove(x)
            else:
                new_ver=set(ver)
                new_ver.add(end)
                new_nh=A.dyn_nh(nh,x,end)
                P=A.algo(new_sub,new_nh,new_ver)
                result=result+ P
                A.remove_edge(x,cop=False)
                nh.remove(x)
            
            #if not A.connected(): break
        for e in temp:
            A.connect(e[1][0],e[1][1],e[0])
        #print(result,sub)
        return result    
 
    def number_of_loops(self):
        #returns dimension of the first homology
        start=next(iter(self.ver.keys()))
        stack=[start]
        visited=set()
        counter=0
        while stack:
            
            x=stack.pop()
            if x not in visited:
                counter+=1
                visited.add(x)
                nh=self.ver[x].nh
                nh=set([x[0] for x in nh])
                nh=nh-visited
                stack.extend(nh)
            
        return len(self.edge)-counter+1
    def size_span(self):
        #returns number of edges a spanning tree
        return len(self.edge)-self.number_of_loops()
    
        

    
    def dfs(self,start,end,i,num,lowpt):
        #Base of ROBERT TARJAN's algortighm to check if a graph is 2 vertex connected
        temps=start
        tempe=copy.copy(end)
        i=i+1
        num[end]=i
        lowpt[end]=num[end]
        for w in self.ver[end].nh:
            if w[0] not in num:
                res=self.dfs(end,w[0],i,num,lowpt)
                if res==False: return False
                lowpt[end]=min(lowpt[end],lowpt[w[0]])
                if lowpt[w[0]]>=num[end]: return False
                
            elif w[0]!=start and num[w[0]]< num[end]:
                lowpt[end]=min(lowpt[end],num[w[0]])
        
               
        return True
    
    def bicon(self):
        #ROBERT TARJAN's algorithm, checks if graph is 2-vertex connected
        start=next(iter(self.ver))
        ends=self.ver[start].nh
        ends=[x[0] for x in ends]
        end=ends[0]
        num={start:0}
        lowpt={start:0}
        result=self.dfs(start,end,0,num,lowpt)
        if len(num)< len(self.ver):return False
        
        return result
        

    def complement_sp(self):
        #returns numpy array where each row represent complement of a spanning tree
        #works if edges are labeled by 0,...,n ; any method using this will not work without this condition
        A=self.binary_sp()
        N=len(A)
        M=len(self.edge)
        result=zeros((N,M),dtype=bool)
        for y in range(N):
            temp=bits1(A[y],M)
            result[y,:]=temp   
        
        
        return result.astype(int8)
 
    def sub_2con(self):
        
        #return all 2-vertex connected subgraphs
        
        edges=set(self.edge.keys())
        A=copy.deepcopy(self)
        resul=[]
        for x in edges:
            nh=set(A.nh([x]))
            ver=set([A.edge[x][0],A.edge[x][1]])
            resul=resul+A.algo(set([x]),nh,ver)
            A.remove_edge(x,cop=False)
        
        
        
        result=[x for x in resul if self.to_graph(list(x[0])).bicon()]
        
        for edge in self.edge:
            result.append((set([edge]),set([self.edge[edge][0],self.edge[edge][1]])))
        
        return result


    def facets(self):
        #returns facets of polytope
        A=self.sub_2con()
        N=len(A)
        M=len(self.edge)+1
        result=zeros((N+1,M),dtype=int8)
        for x in range(N):
            for y in A[x][0]:
                result[x,y]+=1
            result[x,-1]=   -len(A[x][0]) +len(A[x][1])-1
        result[-1,:-1]=-ones(M-1)
        result[-1,-1]=len(self.edge)-len(self.ver)+2
        return result
                
    def lattice_points(self):
        #returns all latice points of the polytope
        N=len(self.edge)+1
        A=self.complement_sp()
        M=len(A)
        A=hstack((A,ones((M,1),dtype=int8)))
        B=zeros((N,N),dtype=int8)
        for i in range(N-1):
            B[i,i]=1
        result=zeros((N*M,N),dtype=int8)
        for x in range(M):
            for y in range(N):
                result[y+x*N]=A[x]+B[y]
        
        b=ascontiguousarray(result).view(dtype((void, result.dtype.itemsize * result.shape[1])))
        _, idx = unique(b, return_index=True)
        result = result[idx]
        return result
       
    def div_sub(self,D=4):
        #returns all div subgraphs
        X=self.sub_2con()
        Y=[x[0] for x in X if len(x[0])-(D//2)*len(x[1])+(D//2)>=0]
        return Y
    def div_facets(self,D=4,alpha=[inf]):
        #returns all divergent facets
        facets=self.facets()
        if alpha[0] ==inf:
            V=ones(len(self.edge)+1,dtype=int8)
            V[-1]=D//2
            ind=where(facets.dot(V)<=0)
            return facets[ind]
        
        ind=where(facets.dot(alpha)<=0)
        return facets[ind]
    def connected_comp(self):
        #returns a connected component of a graph
        
        start=next(iter(self.ver))
        stack=[start]
        visited=set()
        while stack:
            vertex=stack.pop()
            if vertex not in visited:
                visited.add(vertex)
                nh=(self.ver[vertex].nh)
                nh1=([x[0] for x in nh ])
                nh=set(nh1)
                stack.extend(nh-visited)
        return visited
        
   
    def integra(self,A,l,momentum,mass):
        #returns regularized integral
        div=self.div_facets(alpha=A)
        #print(div)
        if len(div)==0:
            d=sympy.symbols("K"+str(A).replace(",","").replace(" ", "_").replace("]", "+e]"  ))
            return d
        result=0
        facet=div[-1]
        not_on_facet_index= where(self.lattice_points().dot(facet)>0)
        not_on_facet=self.lattice_points()[not_on_facet_index]
       # print(not_on_facet,len(not_on_facet))
       
        if facet.dot(A)==0:
           # print(facet[-1])
            e=(sympy.symbols("e")**(-1) )* (sympy.Rational(1,int(facet[-1])))
            
            
        else: e=facet.dot(A)**(-1)
        for x in not_on_facet:
            
            
            result= sympy.Add(result,(A[-1]+sympy.symbols("e"))*e*self.coef_of_cut(x[:-1],l,mass,momentum)*(int(facet.dot(x)))*(self.integra(A+x,l,momentum,mass)))
        
        return result
    
            
    def coef_of_cut(self,cut,l,mass,momentum):
        #returns coefficient of a monomial in first or second Symanzik polynomials
        if tuple(cut) in self.coef: return self.coef[tuple(cut)]
        if sum(cut)==l:
            self.coef[tuple(cut)]=1
            return 1
        for edge in range(len(cut)):
            if cut[edge]==2:
                self.coef[tuple(cut)]=mass[edge]*mass[edge]
                return mass[edge]*mass[edge]
        edges, =where(cut==1)
        edges=list(edges)

        
        def power_replace(x):
            
            return x.group(1)+x.group(1)
        def number_space(x):
            return x.group(0)[0]+"*"
        A=copy.deepcopy(self)
        for edge in edges:
            A.remove_edge(edge,cop=False)
      
        V_1=A.connected_comp()
        
        V_2=set(self.ver)-V_1
        
        result=0
        for vertex in V_1:
            result+= momentum[vertex]
        if result==0:
            return result
        result =result*result
        
        result=(" "+str(sympy.expand(result))).replace("**2","^")
        
        result=re.sub(r"\s(\w+)\^",power_replace,result)
        
        result=re.sub("\s([0-9\.]+)\*",r"\1^",result)
        
        result=result.replace("*","")
        
        result=result.replace("^","*")
        

        
        

        result=parse_expr(result)
        edges,=list(where(cut==1))
        for edge in edges:
            if ((self.edge[edge][0] in V_1) and (self.edge[edge][1] in V_2)) or ((self.edge[edge][1] in V_1) and (self.edge[edge][0] in V_2)):
                result += mass[edge]*mass[edge]
        self.coef[tuple(cut)]=result
        return result
    

    
    def draw(self):
        #draws the graph using networkx
        G=nx.Graph()
        A=self.data()
        ver=list(self.ver.keys())
        edges=zip(list(A[1]),list(A[2]))
        G.add_nodes_from(ver)
        G.add_edges_from(edges)
        pos=nx.circular_layout(G)
        nx.draw_networkx(G,pos)
        dic={}
        for x in range(len(A[0])):
            if (A[1][x],A[2][x]) not in dic :dic[(A[1][x],A[2][x])]=[A[0][x]]
            else:dic[(A[1][x],A[2][x])]=dic[(A[1][x],A[2][x])]+[A[0][x]]
            
        nx.draw_networkx_edge_labels(G,pos=pos,edge_labels=dic)
        plt.show()
        
        
    def data(self):
        #return data of the graph
        return vstack((array(list(self.edge)),array(list(self.edge.values())).transpose()))

def Amplitude(G,Final_ver=0,D=4,momentum=None,mass=None):
        # takes a graph and returns it's e-expansion, based on http://arxiv.org/abs/1605.04970
        # takes two dictionaries for masses and momenta and sets graph masses and momenta to that
        # if no dictionary is given uses the graph's own dictionary for masses and momenta
        # if graph dictionaries are empty sets all masses to symbol 'm' and momenta to zero
        if not G.bicon(): print("The graph is not 2-vertex connected"); return None
        if momentum==None and G.momentum=={}:
            
            momentum={}
            for v in G.ver:
                momentum[v]=0
            G.momentum=momentum
            G.coef={}
        elif momentum!=None:
            
            for x in momentum:
                if type(momentum[x])== type("asd") :
                    if momentum[x][0]=="-": momentum[x]=-sympy.symbols(momentum[x][1:])
                    else: momentum[x]=sympy.symbols(momentum[x])
            for v in G.ver:
                if v not in momentum:
                    momentum[v]=0
            for v in G.ver:
                if v!= Final_ver: momentum[Final_ver]-=momentum[v]
            G.momentum=momentum
            G.coef={}
        
            
        if mass==None and G.mass=={}:
            mass={}
            for v in G.edge:
                mass[v]=sympy.symbols('m')
            G.mass=mass
            G.coef={}
        elif mass!=None :
            mass=G.mass
            for e in mass:
                 if type(mass[e])== type("asd") :mass[e]=sympy.symbols(mass[e])
            for e in G.edge:
                if e not in mass:
                    mass[e]=0
            G.mass=mass
            G.coef={}
        momentum=G.momentum
        mass=G.mass
        print("Graph edges:","\n\n" ,G.edge,"\n")
                
        print("Momenta:",momentum,"Masses:",mass,"\n")
 
            
        
        
        

        A=ones(len(G.edge)+1,dtype=int8)
        A[-1]=D//2
        l=G.number_of_loops()
        edge_var={}
        for a in G.edge:
            edge_var[a]=sympy.symbols("t"+str(a))
            
        def monomial(x):
            temp=1
            for y in range(len(x)):
                temp*=edge_var[G.data()[0][y]]**int(x[y])
            return temp
        f=0
        for x in G.lattice_points():
            
            f+= G.coef_of_cut(x[:-1],l,mass,momentum)*monomial(x[:-1])
        print("f"+str(list(edge_var.values()))+"=", f,"\n\n")
        print("K[A]= integral over real positive t_i's of    t^A[0:"+str(len(G.edge)-1)+"] / f^A["+str(len(G.edge))+"] dt0/t0 ... d"+str(list(edge_var.values())[-1])+"/"+str(list(edge_var.values())[-1]),"\n\n")
        print("where t^A[0:"+str(len(G.edge)-1)+"] = t0^A[0] ... "+str(list(edge_var.values())[-1])+"^A["+str(len(G.edge)-1)+"]","\n\n\n")
            
        
        return G.integra(A,l,momentum,mass)



def complete_graph(k):

    #returns complete graph on k nodes
    a=graph(n=k)
    for x in a.ver:
        for y in a.ver:
            if x< y: a.connect(x,y)
    return a

hat=graph(n=3)
hat.connect(0,1)
hat.connect(0,2)
hat.connect(1,2)
hat.connect(1,2)

print(Amplitude(hat))



                        

                        
