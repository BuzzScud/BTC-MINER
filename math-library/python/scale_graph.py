"""Exact rod towers, formula evaluation and multiplicative magnitude scales.

Definitions follow the pinned FractalAbacus source. This is a tested runtime
translation, not Lean-extracted code. Projection loses high digits; refinement
re-evaluates the retained formula with its exact inputs. Read-back requires a
known interval narrower than capacity. Scale is separate from tower depth.
"""
from dataclasses import dataclass
from fractions import Fraction
from math import gcd, prod


def integer(value):
    if type(value) is not int: raise ValueError('Expected an exact integer')
    return value


def on_rod(formula, inputs, modulus):
    if type(formula) is int: return formula%modulus
    if isinstance(formula,str): return integer(inputs[formula])%modulus
    if not isinstance(formula,tuple) or not formula: raise ValueError('Invalid formula')
    op,*args=formula
    if op=='pow' and len(args)==2:
        exponent=integer(args[1])
        if exponent<0: raise ValueError('Polynomial exponents must be nonnegative')
        return pow(on_rod(args[0],inputs,modulus),exponent,modulus)
    if op not in ('add','sub','mul') or len(args)!=2: raise ValueError('Unsupported rod formula')
    a,b=(on_rod(x,inputs,modulus) for x in args)
    return (a+b if op=='add' else a-b if op=='sub' else a*b)%modulus


def formula_bounds(formula, bounds):
    if type(formula) is int: return formula,formula
    if isinstance(formula,str): return bounds[formula]
    op,*args=formula
    if op=='pow' and len(args)==2:
        lo,hi=formula_bounds(args[0],bounds); exponent=integer(args[1])
        if exponent<0: raise ValueError('Polynomial exponents must be nonnegative')
        values=[lo**exponent,hi**exponent]
        if lo<=0<=hi: values.append(0**exponent)
        return min(values),max(values)
    if op not in ('add','sub','mul') or len(args)!=2: raise ValueError('Unsupported rod formula')
    a,b=formula_bounds(args[0],bounds); c,d=formula_bounds(args[1],bounds)
    if op=='add': return a+c,b+d
    if op=='sub': return a-d,b-c
    values=(a*c,a*d,b*c,b*d)
    return min(values),max(values)


@dataclass(frozen=True)
class Frame:
    bases: tuple
    depths: tuple

    def __post_init__(self):
        if not isinstance(self.bases,tuple) or not isinstance(self.depths,tuple): raise ValueError('Use immutable base and depth tuples')
        if not self.bases or len(self.bases)!=len(self.depths): raise ValueError('One depth is required per base')
        if any(type(b) is not int or b<2 for b in self.bases): raise ValueError('Bases must be integers at least two')
        if any(type(d) is not int or d<0 for d in self.depths): raise ValueError('Depths must be nonnegative integers')
        if any(gcd(a,b)!=1 for i,a in enumerate(self.bases) for b in self.bases[i+1:]): raise ValueError('Bases must be pairwise coprime')

    @property
    def moduli(self): return tuple(b**d for b,d in zip(self.bases,self.depths))
    @property
    def capacity(self): return prod(self.moduli)

    def deepen(self,index):
        if type(index) is not int or not 0<=index<len(self.bases): raise ValueError('Invalid rod index')
        ds=list(self.depths); ds[index]+=1
        return Frame(self.bases,tuple(ds))

    def encode(self,value,bounds=None):
        value=integer(value); lo,hi=(value,value) if bounds is None else bounds
        if any(type(v) is not int for v in (lo,hi)) or not lo<=value<=hi: raise ValueError('Value outside its declared bound')
        return Column(self,tuple(value%m for m in self.moduli),(lo,hi))

    def evaluate(self,formula,inputs,bounds):
        for name,value in inputs.items():
            integer(value);lo,hi=bounds[name]
            if any(type(v) is not int for v in (lo,hi)) or not lo<=value<=hi: raise ValueError('Input outside its declared bound')
        values=tuple(on_rod(formula,inputs,m) for m in self.moduli)
        return Column(self,values,formula_bounds(formula,bounds))

    def fibre(self,index,residue):
        if type(index) is not int or not 0<=index<len(self.bases): raise ValueError('Invalid rod index')
        m=self.moduli[index]
        if type(residue) is not int or not 0<=residue<m: raise ValueError('Noncanonical residue')
        return range(residue,self.bases[index]*m,m)

    def description(self):
        return dict(bases=list(self.bases),depths=list(self.depths),moduli=list(self.moduli),capacity=self.capacity)


@dataclass(frozen=True)
class Column:
    frame: Frame
    residues: tuple
    bounds: tuple

    def __post_init__(self):
        if len(self.residues)!=len(self.frame.bases) or any(type(r) is not int or not 0<=r<m for r,m in zip(self.residues,self.frame.moduli)):
            raise ValueError('Noncanonical residue column')
        if len(self.bounds)!=2 or any(type(x) is not int for x in self.bounds) or self.bounds[0]>self.bounds[1]: raise ValueError('Invalid read-back interval')

    def project(self,target):
        if target.bases!=self.frame.bases or any(a>b for a,b in zip(target.depths,self.frame.depths)):
            raise ValueError('Projection requires a shallower level on the same bases')
        return Column(target,tuple(r%m for r,m in zip(self.residues,target.moduli)),self.bounds)

    def canonical(self):
        """Read the finite quotient representative, not an unbounded integer."""
        value=0; capacity=1
        for r,m in zip(self.residues,self.frame.moduli):
            if m==1: continue
            value+=capacity*((r-value)*pow(capacity,-1,m)%m)
            capacity*=m
        return value

    def readback(self):
        lo,hi=self.bounds; M=self.frame.capacity
        if hi-lo>=M: raise ValueError('Capacity does not uniquely cover the read-back interval; deepen and re-evaluate')
        value=lo+(self.canonical()-lo)%M
        if value>hi: raise ArithmeticError('Residues contradict the declared interval')
        return value


@dataclass(frozen=True)
class FormulaValue:
    formula: object
    scale: int=1

    def __post_init__(self):
        if type(self.scale) is not int or self.scale<1: raise ValueError('Magnitude scale must be a positive integer')

    def column(self,frame,inputs,bounds): return frame.evaluate(self.formula,inputs,bounds)
    def value(self,frame,inputs,bounds): return Fraction(self.column(frame,inputs,bounds).readback(),self.scale)

    def rescale(self,factor):
        if type(factor) is not int or factor<1: raise ValueError('Scale factor must be a positive integer')
        return FormulaValue(('mul',factor,self.formula),factor*self.scale)

    def multiply(self,other): return FormulaValue(('mul',self.formula,other.formula),self.scale*other.scale)


def traversal_trace(phase,cell_phase,prime,labels,index=0):
    """The same two-stage rod formulas used by the native nonce generator."""
    cell_index,label_index=divmod(index,360)
    cell_frame=Frame((2,3,5),(4,0,2))
    cell_formula=('add','cell_phase',('mul','prime','i'))
    cell_inputs={'cell_phase':cell_phase,'prime':prime,'i':cell_index}
    cell_bounds={'cell_phase':(0,399),'prime':(prime,prime),'i':(0,399)}
    cell_column=cell_frame.evaluate(cell_formula,cell_inputs,cell_bounds)
    cell=cell_column.canonical()
    target=Frame((2,3,5),(7,2,3)); deep=target.deepen(0)
    formula=('add',('add',('mul',360,'cell'),'phase'),'label')
    inputs={'cell':cell,'phase':phase,'label':int(labels[label_index])}
    bounds={'cell':(0,399),'phase':(0,143999),'label':(0,359)}
    result=deep.evaluate(formula,inputs,bounds)
    coarse=result.project(target); direct=target.evaluate(formula,inputs,bounds)
    if coarse.residues!=direct.residues: raise ArithmeticError('Tower projection failed')
    return {'index':index,'cell_frame':cell_frame.description(),'cell_residues':list(cell_column.residues),
            'cell':cell,'formula':formula,'inputs':inputs,'magnitude_scale':1,
            'deep_frame':deep.description(),'deep_residues':list(result.residues),
            'readback_bound':list(result.bounds),'unwrapped_value':result.readback(),
            'target_frame':target.description(),'projected_residues':list(coarse.residues),
            'offset':coarse.canonical(),'projection_matches_shallow_evaluation':True}
