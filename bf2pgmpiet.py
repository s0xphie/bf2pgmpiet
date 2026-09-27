#!/usr/bin/env python3
"""
fbf_compiler.py -- folded (squarish) Brainfuck -> pgmpiet compiler, WITH loops.

Not one long row: the program is cut only at bracket-depth-0 boundaries into
segments that are stacked and joined by tape-neutral push+pointer carriage-
return connectors, so every segment reuses the verified horizontal loop
detours while the overall image stays roughly square.  A white leader keeps
the interpreter's fixed top-left start pointing at the program.

Correct Piet colour rule (hue*3+lightness; command = hue-change*3 + light-change).
Self-contained: needs only the standard library.

Usage:
    python3 fbf_compiler.py program.bf [tape_size]   # -> fbf_out.pgm  (P5)
    python3 fbf_compiler.py "++[>+++<-]>." [tape_size]
"""
import sys, os, math

STEPS=[112,131,134,148,155,162,170,177,184,191,198,205,212,219,226,233,240,247]
BLACK,WHITE=33,255
VEC={0:(1,0),1:(0,1),2:(-1,0),3:(0,-1)}
CMD={'push':1,'pop':2,'add':3,'subtract':4,'multiply':5,'divide':6,'mod':7,'not':8,'greater':9,
     'pointer':10,'switch':11,'duplicate':12,'roll':13,'in_number':14,'in_char':15,'out_number':16,'out_char':17}
C=CMD
def next_step(s,c): return ((s//3+c//3)%6)*3 + (s%3+c%3)%3
def prev_step(s,c): return ((s//3-c//3)%6)*3 + (s%3-c%3)%3
def col(step): return STEPS[step]
def chain_deltas(r): return cdeltas(r)+[C['pointer']]
def cdeltas(n):
    if n==0: return [C['push'],C['not']]
    d=[C['push']]
    for b in bin(n)[3:]:
        d+=[C['duplicate'],C['add']]
        if b=='1': d+=[C['push'],C['add']]
    return d


class Compiler:
    def __init__(self, tape_size=300):
        self.T = tape_size
        self.row = [0]
        self.cur = 0

    def emit(self, delta):
        self.cur = next_step(self.cur, delta)
        self.row.append(self.cur)
        return len(self.row) - 1

    def emit_free(self):
        """Place a fresh pixel with no incoming Delta constraint (used
        right after a white gap); self.cur is whatever the caller set."""
        self.row.append(self.cur)
        return len(self.row) - 1

    def push_literal(self, n):
        self.emit(CMD['push'])
        bits = bin(n)[2:]
        for b in bits[1:]:
            self.emit(CMD['duplicate']); self.emit(CMD['add'])
            if b == '1':
                self.emit(CMD['push']); self.emit(CMD['add'])

    def init_tape(self):
        for _ in range(self.T):
            self.emit(CMD['push']); self.emit(CMD['not'])

    def gt(self):
        self.push_literal(self.T); self.push_literal(1); self.emit(CMD['roll'])

    def lt(self):
        self.push_literal(self.T); self.push_literal(self.T - 1); self.emit(CMD['roll'])

    def plus(self):
        self.push_literal(1); self.emit(CMD['add'])

    def minus(self):
        self.push_literal(1); self.emit(CMD['subtract'])

    def dot(self):
        self.emit(CMD['duplicate']); self.emit(CMD['out_char'])

    def comma(self):
        self.emit(CMD['pop']); self.emit(CMD['in_char'])

    def compile(self, bf_source):
        self.init_tape()
        open_stack = []
        self.loops = []  # {'x_open_ptr','x_body','x_close_ptr','x_after','depth'}
        self.max_depth = 0
        depth = 0
        for c in bf_source:
            if c == '>': self.gt()
            elif c == '<': self.lt()
            elif c == '+': self.plus()
            elif c == '-': self.minus()
            elif c == '.': self.dot()
            elif c == ',': self.comma()
            elif c == '[':
                depth += 1
                self.max_depth = max(self.max_depth, depth)
                self.emit(CMD['duplicate']); self.emit(CMD['not'])
                x_ptr = self.emit(CMD['pointer'])
                self.row.append('WHITE')
                self.cur = 0
                x_body = self.emit_free()
                open_stack.append({'x_open_ptr': x_ptr, 'x_body': x_body, 'depth': depth})
            elif c == ']':
                info = open_stack.pop()
                self.emit(CMD['duplicate']); self.emit(CMD['not']); self.emit(CMD['not'])
                x_ptr2 = self.emit(CMD['pointer'])
                self.row.append('WHITE')
                self.cur = 0
                x_after = self.emit_free()
                info['x_close_ptr'] = x_ptr2
                info['x_after'] = x_after
                self.loops.append(info)
                depth -= 1
        assert not open_stack, "unbalanced brackets"
        return self.row, self.loops



class GridBuilder:
    ROW_MAIN, ROW_APPROACH = 0, 1
    DEPTH_BUDGET = 12  # rows reserved per nesting depth for turn chains

    def turn_start_row(self, depth):
        return 3 + (depth - 1) * self.DEPTH_BUDGET

    def __init__(self, row, loops):
        self.row0 = row
        self.loops = loops
        self.width = len(row)
        self.cells = {}  # (x,y) -> gray value (int)

    def set(self, x, y, gray):
        self.cells[(x, y)] = gray
        self.width = max(self.width, x + 1)

    def build(self):
        # row0: main program (row0 entries are either int step values or
        # the string 'WHITE' for the fall-through gaps)
        for x, step in enumerate(self.row0):
            if step == 'WHITE':
                self.set(x, self.ROW_MAIN, WHITE)
            else:
                self.set(x, self.ROW_MAIN, col(step))

        approach_targets = {}  # column -> fixed marker colour (step)
        for lp in self.loops:
            approach_targets[lp['x_body']] = self.row0[lp['x_body']]
            approach_targets[lp['x_after']] = self.row0[lp['x_after']]

        for lp in self.loops:
            self._build_skip_forward(lp)
            self._build_loop_back(lp)

        # Final approach, per target column: row2 = free cell (climb's
        # white slide ends here, command-less), row1 = push cell (its
        # own exit fires push, using row2's size=1), row0 = the marker
        # itself (entered via pointer from row1). Both row1/row2 values
        # are derived BACKWARD from the marker's already-fixed colour.
        for x, marker_step in approach_targets.items():
            cell2 = prev_step(marker_step, CMD['pointer'])
            cell1 = prev_step(cell2, CMD['push'])
            self.set(x, 2, col(cell1))
            self.set(x, 1, col(cell2))

        # fill remaining row1/row2 cells with white (horizontal/vertical
        # slide paths use whatever's left over)
        for y in (1, 2):
            for x in range(self.width):
                if (x, y) not in self.cells:
                    self.set(x, y, WHITE)

        return self._to_grid()

    def _lay_chain_vertical(self, x, y0, r, base_colour):
        """A white-entered cell first (its colour is `base_colour`,
        arbitrary -- no real Delta fires getting here), THEN the real
        push_literal(r)+pointer chain, whose deltas fire on each
        subsequent transition. Returns the row of the final (pointer)
        cell."""
        cur = base_colour
        self.set(x, y0, col(cur))
        y = y0 + 1
        for d in chain_deltas(r):
            cur = next_step(cur, d)
            self.set(x, y, col(cur))
            y += 1
        return y - 1

    def _lay_chain_horizontal(self, x0, y, r, direction, base_colour):
        """Same fix, horizontally: a white-entered free cell, then the
        real chain."""
        cur = base_colour
        self.set(x0, y, col(cur))
        x = x0 + direction
        for d in chain_deltas(r):
            cur = next_step(cur, d)
            self.set(x, y, col(cur))
            x += direction
        return x - direction

    def _white_vrange(self, x, y_from, y_to):
        lo, hi = sorted((y_from, y_to))
        for y in range(lo, hi + 1):
            if (x, y) not in self.cells:
                self.set(x, y, WHITE)

    def _white_hrange(self, y, x_from, x_to):
        lo, hi = sorted((x_from, x_to))
        for x in range(lo, hi + 1):
            if (x, y) not in self.cells:
                self.set(x, y, WHITE)

    def _build_skip_forward(self, lp):
        x_open = lp['x_open_ptr']
        x_target = lp['x_after']
        base_colour = self.row0[x_open]
        row_start = self.turn_start_row(lp['depth'])
        # descent from row3 down to row_start-1 passes through shallower
        # depths' row-bands, which default to black; must be explicitly
        # whited at this specific (unique) column.
        for y in range(3, row_start):
            if (x_open, y) not in self.cells:
                self.set(x_open, y, WHITE)
        # turn1: down -> right, r=3, at column x_open (free-entry + 6-cell chain)
        end_row = self._lay_chain_vertical(x_open, row_start, 3, base_colour)
        # turn2: right -> UP needs r=3 (right+3=up); the chain is free-entry +
        # chain_deltas(3) [6 cells] so its pointer lands at t2_start+6; we want
        # that pointer at x_target so the climb happens in the marker column.
        t2_start = x_target - 6
        self._white_hrange(end_row, x_open + 1, t2_start - 1)
        self._lay_chain_horizontal(t2_start, end_row, 3, +1, 0)
        # climb white from just below the approach cells up to just above turn2
        self._white_vrange(x_target, 3, end_row - 1)

    def _build_loop_back(self, lp):
        x_close = lp['x_close_ptr']
        x_target = lp['x_body']
        base_colour = self.row0[x_close]
        row_start = self.turn_start_row(lp['depth'])
        for y in range(3, row_start):
            if (x_close, y) not in self.cells:
                self.set(x_close, y, WHITE)
        # turn1: down -> left, r=1, at column x_close (free-entry + 2-cell chain)
        end_row = self._lay_chain_vertical(x_close, row_start, 1, base_colour)
        # turn2 (left -> up), 3 cells, ending exactly at x_target, starts at x_target+2
        t2_start = x_target + 2
        self._white_hrange(end_row, t2_start + 1, x_close - 1)
        self._lay_chain_horizontal(t2_start, end_row, 1, -1, 0)
        # climb white
        self._white_vrange(x_target, 3, end_row - 1)

    def _colour_before(self, x, y):
        """Colour of whatever's immediately 'before' (x,y) in its own
        chain -- since (x,y) itself is about to be white (approached via
        slide), we just need *a* valid free starting colour; 0 is fine,
        it's never entered via a real Delta."""
        return 0

    def _peek(self, x, y):
        return self.cells.get((x, y))

    def _to_grid(self):
        H = max(y for (_, y) in self.cells) + 3
        W = self.width
        grid = [[BLACK] * W for _ in range(H)]
        for (x, y), v in self.cells.items():
            grid[y][x] = v
        return W, H, grid



class Cur:
    """Places white slides and tape-neutral push+pointer turns. Every turn
    begins with a free-entry codel (so a preceding white slide never eats
    the turn's first push)."""
    def __init__(s,cells,x,y,d,color): s.c=cells;s.x=x;s.y=y;s.d=d;s.col=color
    def _step(s):
        dx,dy=VEC[s.d]; s.x+=dx; s.y+=dy
    def white(s,n):
        for _ in range(n):
            s._step()
            if (s.x,s.y) not in s.c: s.c[(s.x,s.y)]=WHITE
    def turn(s,k):
        s._step(); s.c[(s.x,s.y)]=STEPS[s.col]           # free entry (color unchanged)
        for delt in cdeltas(k)+[C['pointer']]:
            s._step(); s.col=next_step(s.col,delt); s.c[(s.x,s.y)]=STEPS[s.col]
        s.d=(s.d+k)%4
    def free(s):
        s._step(); s.c[(s.x,s.y)]=STEPS[s.col]
    def op(s,cmd):
        s._step(); s.col=next_step(s.col,C[cmd]); s.c[(s.x,s.y)]=STEPS[s.col]


def connect_fixed(cells, ex, ey, color, block_a_bottom, LM):
    """From (ex,ey) flowing RIGHT, carriage-return to arrive at (LM, R)
    flowing RIGHT, where R is chosen by the connector's own extent.
    Returns R.  Requires LM>=8."""
    cur=Cur(cells, ex, ey, 0, color)
    cur.white(1); cur.turn(1)                          # right->down
    cur.white((block_a_bottom+2)-cur.y); cur.turn(1)   # down (clear block A) -> left
    cur.white(cur.x-LM); cur.turn(3)                   # left -> down (col LM-7)
    cur.white(1); cur.turn(3)                          # down -> right
    cur.white((LM-1)-cur.x)                            # right to (LM-1,R)
    return cur.y


class SegCompiler(Compiler):
    def move(self, net):
        # coalesced >/< : roll(T, net mod T) in one op
        rv = net % self.T
        if rv == 0: return
        self.push_literal(self.T); self.push_literal(rv); self.emit(C['roll'])
    def addN(self, net):
        # coalesced +/- : single add/subtract of |net|
        if net > 0: self.push_literal(net); self.emit(C['add'])
        elif net < 0: self.push_literal(-net); self.emit(C['subtract'])
    def compile(self,bf):
        self.loops=[]; st=[]; depth=0; self.maxdepth=0; self.bnd=[]
        for _ in range(self.T):
            self.emit(C['push']); self.emit(C['not']); self.bnd.append(len(self.row))
        i=0; n=len(bf)
        while i<n:
            ch=bf[i]
            if ch in '<>':
                net=0
                while i<n and bf[i] in '<>':
                    net += 1 if bf[i]=='>' else -1; i+=1
                self.move(net)
            elif ch in '+-':
                net=0
                while i<n and bf[i] in '+-':
                    net += 1 if bf[i]=='+' else -1; i+=1
                self.addN(net)
            elif ch=='.': self.dot(); i+=1
            elif ch==',': self.comma(); i+=1
            elif ch=='[':
                depth+=1; self.maxdepth=max(self.maxdepth,depth)
                self.emit(C['duplicate']); self.emit(C['not']); xp=self.emit(C['pointer'])
                self.row.append('WHITE'); self.cur=0; xb=self.emit_free()
                st.append({'x_open_ptr':xp,'x_body':xb,'depth':depth}); i+=1
            elif ch==']':
                info=st.pop()
                self.emit(C['duplicate']); self.emit(C['not']); self.emit(C['not']); xp=self.emit(C['pointer'])
                self.row.append('WHITE'); self.cur=0; xa=self.emit_free()
                info['x_close_ptr']=xp; info['x_after']=xa; self.loops.append(info); depth-=1; i+=1
            else: i+=1
            if depth==0: self.bnd.append(len(self.row))
        assert not st,"unbalanced []"
        return self.row,self.loops,self.bnd


def build(row, loops, bnd, S, LM=8):
    # choose segment end indices (exclusive) at boundaries ~every S
    cuts=[]; last=0
    for b in bnd:
        if b-last>=S: cuts.append(b); last=b
    segs=[]; prev=0
    for c in cuts:
        if c>prev: segs.append((prev,c)); prev=c
    if prev<len(row): segs.append((prev,len(row)))
    cells={}
    for x in range(LM): cells[(x,0)]=WHITE      # leader
    R=0; blocks=[]
    for si,(a,b) in enumerate(segs):
        if si==0: sub_row=row[a:b]; shift=-a
        else: sub_row=[row[a-1]]+row[a:b]; shift=-a+1
        sub_loops=[]
        for lp in loops:
            if a<=lp['x_open_ptr']<b:
                q={k:(lp[k]+shift if k in ('x_open_ptr','x_body','x_close_ptr','x_after') else lp[k]) for k in lp}
                sub_loops.append(q)
        gb=GridBuilder(sub_row, sub_loops); bw,bh,bgrid=gb.build()
        ox,oy=LM,R
        for y,rr in enumerate(bgrid):
            for x,v in enumerate(rr):
                if v!=BLACK: cells[(ox+x,oy+y)]=v
        exit_x = ox + len(sub_row) - 1            # last main-flow codel
        exit_y = oy
        last_color = row[b-1] if row[b-1]!='WHITE' else 0
        blocks.append((ox,oy,bw,bh,exit_x,exit_y,last_color))
        if si < len(segs)-1:
            R = connect_fixed(cells, exit_x, exit_y, last_color, oy+bh-1, LM)
    # trap after last block: place well to the right of ALL content so the
    # C cell's neighbours are genuinely black (not the approach white flood)
    ox,oy,bw,bh,ex,ey,lc = blocks[-1]
    Xe = max(x for x,_ in cells) + 3
    for x in range(ex+1, Xe): cells[(x,ey)]=WHITE     # white path along exit row
    cells[(Xe,ey)]=STEPS[lc]                            # E (entered via white going right)
    cells[(Xe,ey+1)]=STEPS[lc]                          # D below E
    cells[(Xe-1,ey+1)]=STEPS[lc]                        # C left of D  (left nbr is black)
    xs=[x for x,_ in cells]; ys=[y for _,y in cells]
    W=max(xs)+1; H=max(ys)+1; g=[[BLACK]*W for _ in range(H)]
    for (x,y),v in cells.items(): g[y][x]=v
    return W,H,g


def auto_tape(bf):
    pos=0; mx=0
    for c in bf:
        if c=='>': pos+=1; mx=max(mx,pos)
        elif c=='<': pos-=1
    return max(4, mx+2)   # +2 buffer, floor 4: avoids ring degeneracy (+1==-1 at T=2) and edge wrap

def compile_to(bf,T,path):
    co=SegCompiler(T); row,loops,bnd=co.compile(bf)
    S=max(24,int(math.ceil(math.sqrt(len(row))*1.5)))
    W,H,g=build(row,loops,bnd,S)
    with open(path,'wb') as f:
        f.write(("P5\n# fbf %dx%d\n%d %d\n255\n"%(W,H,W,H)).encode()); [f.write(bytes(r)) for r in g]
    return W,H

if __name__=='__main__':
    arg=sys.argv[1] if len(sys.argv)>1 else "++[>+++<-]>."
    if os.path.isfile(arg):
        bf=open(arg).read()
        out=os.path.splitext(os.path.basename(arg))[0]+'.pgm'   # match the input name
    else:
        bf=arg; out='fbf_out.pgm'
    T=int(sys.argv[2]) if len(sys.argv)>2 else auto_tape(bf)
    W,H=compile_to(bf,T,out); print("compiled -> %dx%d (%s, tape=%d)"%(W,H,out,T))
