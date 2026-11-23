"""Exact rational recomputation of the GdLL (arXiv:2303.01095v2, Section 5) bound for c_{3,1}.
Usage: python3 -I gdll_exact.py <data dir> <d>      (python-flint, exact arithmetic over Q)
Reads only the first block (G_3-invariant polynomials) of polynomials-<d>.txt as text."""
import sys, re, time, json, site
sys.path.append(site.getusersitepackages())   # python-flint lives in the user site; -I hides it
from fractions import Fraction
from flint import fmpq, fmpq_mpoly_ctx, fmpq_mat, Ordering
ctx=fmpq_mpoly_ctx.get(('x','y','z','w'),Ordering.lex)
x,y,z,w=ctx.gens(); Q=fmpq; half=fmpq(1,2)
def C(c): return ctx.constant(fmpq(c)) if not isinstance(c,fmpq) else ctx.constant(c)
def first_block(text):
    text=text.replace('\\\n','').replace('\n',' ')
    i=text.index('['); i=text.index('[',i+1); depth=0; j=i
    while True:
        if text[j]=='[': depth+=1
        elif text[j]==']':
            depth-=1
            if depth==0: break
        j+=1
    inner=text[i+1:j]
    return [s.strip() for s in re.findall(r'\[([^\[\]]*)\]',inner)]
def parse(s):
    assert re.fullmatch(r'[0-9xy+\-*/^ ()]*',s), s[:80]
    s=s.replace('^','**'); s=re.sub(r'(?<!\*\*)\b(\d+)\b',r'Q(\1)',s)
    v=eval(s,{'__builtins__':{}},{'x':x,'y':y,'Q':Q})
    return v if not isinstance(v,fmpq) else C(v)
def sub(p,vals):   # compose p(x<-vals[0],...)
    return p.compose(*vals)
def integ(p,i,a,b):
    if not isinstance(a,type(x)): a=C(a)
    if not isinstance(b,type(x)): b=C(b)
    P=p.integral(i); g=[x,y,z,w]
    u=list(g); u[i]=b; v=list(g); v[i]=a
    return P.compose(*u)-P.compose(*v)
def const(p):
    assert p.total_degree()<=0, "not constant"
    return p.coefficient(0) if len(p) else fmpq(0)
def sqint(p):
    q=p+p.compose(-x-y,x,z,w)+p.compose(y,-x-y,z,w)
    return const(integ(integ(q,1,0,half),0,-half,0))
def tripleint(p,q):
    r=p*q.compose(x+z,y-z,z,w)*(z-1)
    a=integ(integ(r,0,-half-y,half-z),1,-half+z,0)
    b=integ(integ(r,0,-half,half-z),1,0,z)
    c=integ(integ(r,0,-half,half-y),1,z,half)
    t1=integ(a+b+c,2,0,half)
    d=integ(integ(r,0,-half,half-z),1,z-half,half)
    t2=integ(d,2,half,1)
    return const(t1+t2)
def quadint(p,q):
    r=p*q.compose(x-z,y-w,z,w)*w
    a=integ(integ(r,0,-half,z+half),1,w-half,half)
    t1=integ(integ(a,2,-w,-half),3,half,1)
    b=integ(integ(r,0,-half-y+w+z,half-y),1,w-half,half)
    t2=integ(integ(b,2,half-w,0),3,half,1)
    c=integ(integ(r,0,-half,half-y),1,w+z,half)
    d=integ(integ(r,0,w+z-half-y,half-y),1,-z,w+z)
    e=integ(integ(r,0,w+z-half-y,z+half),1,w-half,-z)
    t3=integ(integ(c+d+e,3,-2*z,half-z),2,-half,0)
    f=integ(integ(r,0,-half,half-y),1,-z,half)
    g=integ(integ(r,0,-half,z+half),1,w+z,-z)
    h=integ(integ(r,0,w+z-half-y,z+half),1,w-half,w+z)
    t4=integ(integ(f+g+h,3,-z,-2*z),2,-half,0)
    return const(t1+t2+t3+t4)
def load(datadir,d):
    return [parse(s) for s in first_block(open(f"{datadir}/polynomials-{d}.txt").read())]
if __name__=="__main__":
    datadir,d=sys.argv[1],int(sys.argv[2])
    P=load(datadir,d); n=len(P); print("d=%d: %d invariant polynomials, degrees %s"%(d,n,[p.total_degree() for p in P]),flush=True)
    t0=time.time()
    b=[sqint(p) for p in P]
    M=[[None]*n for _ in range(n)]
    for i in range(n):
        for j in range(i,n):
            v=sqint(P[i]*P[j])+6*tripleint(P[i],P[j])-12*quadint(P[i],P[j])
            M[i][j]=M[j][i]=v
        print(" row",i,"%.1fs"%(time.time()-t0),flush=True)
    A=fmpq_mat(n,n,[M[i][j] for i in range(n) for j in range(n)]); B=fmpq_mat(n,1,b)
    X=A.solve(B)
    xb=sum((X[i,0]*b[i] for i in range(n)),fmpq(0))
    c=2+1/xb
    print("exact optimum in this basis: c31 = 2 + 1/(x.b) =",float(Fraction(int(c.p),int(c.q))))
    print("   as decimal: %s"%(Fraction(int(c.p),int(c.q)).limit_denominator(10**30)))
    json.dump({"d":d,"b":[str(v) for v in b],"M":[[str(v) for v in row] for row in M],"x":[str(X[i,0]) for i in range(n)],"c":str(c)},open(f"gdll_exact_d{d}.json","w"))
    print("total %.1fs"%(time.time()-t0))
