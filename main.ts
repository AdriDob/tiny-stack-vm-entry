// tiny-stack-vm entry: faithful ISA v1 interpreter (ISA.md), fast dispatch.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const SMAX = 256, CMAX = 64, MMAX = 256, STEPS = 1e6, OMAX = 65536;

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length;
  const D = new Int32Array(SMAX);
  let sp = 0;
  const C = new Int32Array(CMAX);
  let csp = 0;
  const M = new Int32Array(MMAX);
  const out = new Uint8Array(OMAX);
  let olen = 0, ip = 0, pc = 0, steps = 0;
  const fin = (code: number) => ({ out: out.subarray(0, olen), code });
  const trap = (code: number) => fin(code);
  for (;;) {
    if (steps === STEPS) return trap(10);
    if (pc < 0 || pc >= n) return trap(9);
    const op = p[pc];
    steps++;
    const next = pc + 1;
    // opcode metadata: [immLen, pops, pushes]
    // decoded inline below; bounds check per ISA order:
    // immediate must fit BEFORE executing (rule 4) -> handled per-op
    if (sp < 0) return trap(2); // unreachable, keeps shape
    switch (op) {
      case 0x00: return fin(0);
      case 0x01: {
        if (next >= n) return trap(9);
        if (sp + 1 > SMAX) return trap(3);
        D[sp++] = (p[next] << 24) >> 24; pc = next + 1; break;
      }
      case 0x02: {
        if (next + 4 > n) return trap(9);
        if (sp + 1 > SMAX) return trap(3);
        D[sp++] = p[next] | (p[next+1] << 8) | (p[next+2] << 16) | (p[next+3] << 24);
        pc = next + 4; break;
      }
      case 0x03: if (sp < 1) return trap(2); sp--; pc = next; break;
      case 0x04: if (sp < 1) return trap(2); if (sp + 1 > SMAX) return trap(3); D[sp] = D[sp-1]; sp++; pc = next; break;
      case 0x05: if (sp < 2) return trap(2); { const t = D[sp-1]; D[sp-1] = D[sp-2]; D[sp-2] = t; pc = next; } break;
      case 0x06: if (sp < 2) return trap(2); if (sp + 1 > SMAX) return trap(3); D[sp] = D[sp-2]; sp++; pc = next; break;
      case 0x07: if (sp < 3) return trap(2); { const a=D[sp-3],b=D[sp-2],c=D[sp-1]; D[sp-3]=b;D[sp-2]=c;D[sp-1]=a; pc=next; } break;
      case 0x17: if (sp < 1) return trap(2); D[sp-1] = -D[sp-1] | 0; pc = next; break;
      case 0x1b: if (sp < 1) return trap(2); D[sp-1] = ~D[sp-1]; pc = next; break;
      // binary ALU 0x10..0x22 (excluding 0x17,0x1b)
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        if (sp < 2) return trap(2);
        const b = D[--sp], a = D[sp-1];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13: if (b === 0) return trap(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
          case 0x14: if (b === 0) return trap(4); r = b === -1 ? 0 : (a % b) | 0; break;
          case 0x15: if (b === 0) return trap(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16: if (b === 0) return trap(4); r = ((a >>> 0) % (b >>> 0)) | 0; break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        D[sp-1] = r; pc = next; break;
      }
      case 0x30: case 0x31: case 0x32: {
        if (next + 2 > n) return trap(9);
        const rel = ((p[next] | (p[next+1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { if (sp < 1) return trap(2); const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        pc = take ? next + 2 + rel : next + 2; break;
      }
      case 0x33: {
        if (next + 2 > n) return trap(9);
        if (csp === CMAX) return trap(7);
        C[csp++] = next + 2;
        pc = p[next] | (p[next+1] << 8); break;
      }
      case 0x34: if (csp === 0) return trap(8); pc = C[--csp]; break;
      case 0x40: {
        if (sp < 1) return trap(2);
        const addr = D[sp-1];
        if (addr < 0 || addr >= MMAX) return trap(6);
        D[sp-1] = M[addr]; pc = next; break;
      }
      case 0x41: {
        if (sp < 2) return trap(2);
        const addr = D[sp-1], v = D[sp-2];
        if (addr < 0 || addr >= MMAX) return trap(6);
        sp -= 2; M[addr] = v; pc = next; break;
      }
      case 0x50: {
        if (sp < 1) return trap(2);
        const bytes = new TextEncoder().encode(String(D[--sp]));
        if (olen + bytes.length > OMAX) return trap(11);
        out.set(bytes, olen); olen += bytes.length; pc = next; break;
      }
      case 0x51: {
        if (sp < 1) return trap(2);
        if (olen + 1 > OMAX) return trap(11);
        out[olen++] = D[--sp] & 255; pc = next; break;
      }
      case 0x52: if (sp + 1 > SMAX) return trap(3); D[sp++] = ip < inp.length ? inp[ip++] : -1; pc = next; break;
      case 0x53: if (sp < 1) return trap(2); return fin(D[--sp] & 255);
      default: return trap(5);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
