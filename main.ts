// Driver for the markdown-render-speed-02 entry.
//
// The harness runs `node /bot/main.ts`. It reads the case list from
// /input/cases.json (a JSON array of {id, markdown} objects), renders each
// case on its own with parse() from ./parse.js, and writes /output/html.json
// (a JSON array of HTML strings, one per case, in the cases' order).
// Outside a container, MAKEFUN_INPUT_DIR and MAKEFUN_OUTPUT_DIR stand in
// for /input and /output.

import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

type Case = { id: string; markdown: string };

function inputDir(): string {
  const override = process.env.MAKEFUN_INPUT_DIR;
  return override === undefined || override === '' ? '/input' : override;
}

function outputDir(): string {
  const override = process.env.MAKEFUN_OUTPUT_DIR;
  return override === undefined || override === '' ? '/output' : override;
}

function loadCases(dir: string): Case[] {
  const raw = readFileSync(join(dir, 'cases.json'), 'utf8');
  const parsed: unknown = JSON.parse(raw);
  if (!Array.isArray(parsed)) throw new Error('cases.json is not an array');
  return parsed as Case[];
}

function renderAll(cases: Case[]): string[] {
  const out: string[] = new Array(cases.length);
  for (let k = 0; k < cases.length; k++) {
    out[k] = parse(cases[k].markdown);
  }
  return out;
}

function main(): void {
  const cases = loadCases(inputDir());
  const html = renderAll(cases);
  const dir = outputDir();
  mkdirSync(dir, { recursive: true });
  writeFileSync(join(dir, 'html.json'), JSON.stringify(html));
}

main();
