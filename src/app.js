// ArtFrames editor: one sheet of paper per frame, onion skin, a reference picture or video underneath, a timeline.
import { Stroke } from './brush.js';
import { GPU } from './gpu.js';
import { openVideo } from './video.js';
import { runExport } from './exporter.js';

const af = window.af;
const $ = s => document.querySelector(s);
const $$ = s => [...document.querySelectorAll(s)];
const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
const basename = file => file.split(/[\\/]/).pop();
const stem = name => name.replace(/\.[^.]+$/, '');
const fmtFps = fps => String(Math.round(fps * 100) / 100);
const plural = (n, one, few, many) => {
  const a = n % 10;
  const b = n % 100;
  return a === 1 && b !== 11 ? one : a >= 2 && a <= 4 && (b < 12 || b > 14) ? few : many;
};
const nFrames = n => `${n} ${plural(n, 'кадр', 'кадри', 'кадрів')}`;

const VIDEO_EXT = new Set(['mp4', 'mov', 'm4v', 'webm', 'mkv']);
const IMAGE_EXT = new Set(['png', 'jpg', 'jpeg', 'webp', 'bmp', 'gif']);
const HOLD_W = 16; // px per extra tick in the timeline
const UNDO_LIMIT = 120;

// Graphite, blue and red pencil (construction and corrections, as on a light table), then a few fill colours.
const PALETTE = ['#1b1b1f', '#2f6fde', '#e0453a', '#2a9d5c', '#f2b233', '#ffffff'];

const DEFAULTS = {
  tool: 'round',
  sizes: { round: 6, flat: 22, eraser: 40 },
  color: '#1b1b1f',
  pressure: true,
  smoothing: 0.3,
  angle: 45,
  onion: { on: true, prev: 1, next: 1, opacity: 0.4, prevColor: '#ff3b30', nextColor: '#1fb35a' },
  step: 2,
  loop: true,
  newDoc: { width: 1920, height: 1080, fps: 24 },
};

const prefs = loadPrefs();

function loadPrefs() {
  if (af.env.selftest) return structuredClone(DEFAULTS);
  try {
    const saved = JSON.parse(localStorage.getItem('artframes.prefs') || '{}');
    return {
      ...structuredClone(DEFAULTS),
      ...saved,
      sizes: { ...DEFAULTS.sizes, ...saved.sizes },
      onion: { ...DEFAULTS.onion, ...saved.onion },
      newDoc: { ...DEFAULTS.newDoc, ...saved.newDoc },
    };
  } catch {
    return structuredClone(DEFAULTS);
  }
}

function savePrefs() {
  if (af.env.selftest) return;
  try {
    localStorage.setItem('artframes.prefs', JSON.stringify(prefs));
  } catch {
    // prefs are a convenience
  }
}

// ---------- DOM ----------

const stage = $('#stage');
const sheet = $('#sheet'); // an empty box under the GPU canvas: the paper's shadow and the pointer mapping
const glCanvas = $('#gl');
const strip = $('#strip');
const cursorEl = $('#cursor');
const hud = $('#hud');
const audio = $('#audio');

// ---------- document ----------

let doc = null; // { width, height, fps, paper, frames, file, name }
let ticks = [0]; // start tick of every frame, plus the total at the end
let cur = 0;
// Reference layers under the drawings, bottom first: pictures and VideoRefs, each with { kind, file, name, opacity,
// visible, layer, rect (where it sits before any transform), quad (its four corners on the sheet: top left, top
// right, bottom right, bottom left of the picture) }.
const refs = [];
let sel = null; // the reference the panel and the transform frame work on
let xform = false; // transform mode: the pen moves, scales and rotates the selected reference instead of drawing
let editSketch = false; // the brush draws the own reference (doc.sketch) instead of the current frame
let dirty = false;
let editRev = 0;
let autosavedRev = 0;
let nextId = 1;

const gpu = new GPU(glCanvas, () => contextRestored());

// Colours for the shaders, premultiplied.
const rgb = hex => [1, 3, 5].map(i => parseInt(hex.slice(i, i + 2), 16) / 255);
const rgba = hex => [...rgb(hex), 1];

function makeFrame(hold = 1) {
  return { id: nextId++, hold, layer: null, thumb: null, rev: 0, saved: null };
}

// The own reference: one drawing under every frame (calligraphy to animate over, a path, a layout). It is drawn,
// undone and saved like a frame, but it is not on the timeline.
function makeSketch() {
  return { ...makeFrame(), visible: true, opacity: 0.5 };
}

function ensureLayer(f) {
  if (!f.layer) f.layer = gpu.layer(doc.width, doc.height);
  return f.layer;
}

function recalc() {
  ticks = [0];
  for (const f of doc.frames) ticks.push(ticks[ticks.length - 1] + f.hold);
}

const totalTicks = () => ticks[doc.frames.length];

function frameAtTick(t) {
  let lo = 0;
  let hi = doc.frames.length - 1;
  while (lo < hi) {
    const mid = (lo + hi + 1) >> 1;
    if (ticks[mid] <= t) lo = mid;
    else hi = mid - 1;
  }
  return lo;
}

// GPU memory is not garbage-collected: a replaced document gives back its drawings and its undo history.
function releaseDoc(old, keep) {
  const frames = new Set([...old.frames, old.sketch]);
  for (const e of [...undoStack, ...redoStack]) {
    if (e.type === 'pixels') {
      gpu.free(e.data);
      frames.add(e.frame);
    } else if (e.type === 'struct') {
      for (const snapshot of [e.before, e.after]) for (const [f] of snapshot.frames) frames.add(f);
    }
  }
  for (const f of frames) {
    if (keep.has(f)) continue;
    gpu.free(f.layer);
    f.layer = null;
  }
}

function setDoc({ width, height, fps, paper = '#ffffff', frames = null, sketch = null, file = null }) {
  stopPlayback();
  setXform(false);
  removeAllReferences();
  const fresh = frames || [makeFrame(prefs.step)];
  const own = sketch || makeSketch();
  if (doc) releaseDoc(doc, new Set([...fresh, own]));
  doc = { width, height, fps, paper, frames: fresh, sketch: own, file, name: file ? basename(file) : 'Без назви' };
  editSketch = false;
  undoStack.length = 0;
  redoStack.length = 0;
  sheet.style.width = `${width}px`;
  sheet.style.height = `${height}px`;
  const th = 40;
  strip.style.setProperty('--tw', `${clamp(Math.round((th * width) / height), 24, 96)}px`);
  strip.style.setProperty('--th', `${th}px`);
  for (const f of doc.frames) {
    f.thumb = null;
    if (f.layer) scheduleThumb(f);
  }
  recalc();
  buildStrip();
  fit();
  showFrame(0);
  setDirty(false);
  refreshUI();
}

function pristine() {
  return doc.frames.every(f => !f.layer) && !doc.sketch.layer;
}

// ---------- view: zoom, pan, mirror ----------

const view = { zoom: 1, x: 0, y: 0, mirror: false, fitted: true }; // zoom: screen pixels per document pixel
const dpr = () => devicePixelRatio || 1;
const cssScale = () => view.zoom / dpr();

function applyView() {
  sheet.style.transform = `translate(${view.x}px, ${view.y}px) scale(${cssScale()})`;
  $('#zoomBtn').textContent = `${Math.round(view.zoom * 100)}%`;
  $('#mirrorBtn').classList.toggle('on', view.mirror);
  shapeCursor();
  drawXform();
  requestRender();
}

function fit() {
  const w = stage.clientWidth;
  const h = stage.clientHeight;
  if (!w || !h) return;
  const s = Math.min((w - 56) / doc.width, (h - 56) / doc.height);
  view.zoom = s * dpr();
  view.x = (w - doc.width * s) / 2;
  view.y = (h - doc.height * s) / 2;
  view.fitted = true;
  applyView();
}

function zoomAt(factor, cx, cy) {
  const s0 = cssScale();
  view.zoom = clamp(view.zoom * factor, 0.05, 32);
  const s1 = cssScale();
  view.x = cx - (cx - view.x) * (s1 / s0);
  view.y = cy - (cy - view.y) * (s1 / s0);
  view.fitted = false;
  applyView();
}

new ResizeObserver(() => {
  if (!doc) return;
  if (view.fitted) fit();
  requestRender();
}).observe(stage);

function toDoc(ev, rect) {
  let x = ((ev.clientX - rect.left) / rect.width) * doc.width;
  if (view.mirror) x = doc.width - x;
  return [x, ((ev.clientY - rect.top) / rect.height) * doc.height];
}

// ---------- rendering (GPU) ----------

let renderQueued = false;
// Drawing cost, read by the self-test: input batches (CPU) and full redraws of the sheet.
const perf = { moves: 0, ms: 0, max: 0, renders: 0, renderMs: 0, renderMax: 0 };

let renderAsked = 0;

function requestRender() {
  if (renderQueued) return;
  renderQueued = true;
  renderAsked = performance.now();
  requestAnimationFrame(render);
}

// A reference is drawn through the projective map that takes its picture onto its quad: one matrix covers moving,
// scaling, rotating, mirroring and perspective. The shader gets the inverse, from document uv to picture uv.
function squareToQuad([[x0, y0], [x1, y1], [x2, y2], [x3, y3]]) {
  // Heckbert, "Fundamentals of Texture Mapping and Image Warping" (1989): unit square -> quad, row-major 3x3.
  const sx = x0 - x1 + x2 - x3;
  const sy = y0 - y1 + y2 - y3;
  let g = 0;
  let h = 0;
  if (Math.abs(sx) > 1e-9 || Math.abs(sy) > 1e-9) {
    const dx1 = x1 - x2;
    const dx2 = x3 - x2;
    const dy1 = y1 - y2;
    const dy2 = y3 - y2;
    const den = dx1 * dy2 - dx2 * dy1;
    g = (sx * dy2 - dx2 * sy) / den;
    h = (dx1 * sy - sx * dy1) / den;
  }
  return [x1 - x0 + g * x1, x3 - x0 + h * x3, x0, y1 - y0 + g * y1, y3 - y0 + h * y3, y0, g, h, 1];
}

function invert3([a, b, c, d, e, f, g, h, i]) {
  const A = e * i - f * h;
  const B = f * g - d * i;
  const C = d * h - e * g;
  const det = a * A + b * B + c * C;
  return [A, c * h - b * i, b * f - c * e, B, a * i - c * g, c * d - a * f, C, b * g - a * h, a * e - b * d].map(v => v / det);
}

// Document pixels -> picture uv, cached per quad (a quad is replaced, never edited in place).
function quadInverse(r) {
  if (r.inv?.quad !== r.quad) r.inv = { quad: r.quad, m: invert3(squareToQuad(r.quad)) };
  return r.inv.m;
}

// Where a document point falls on the picture: [u, v], inside when both are in 0..1.
function uvAt(r, x, y) {
  const m = quadInverse(r);
  const w = m[6] * x + m[7] * y + m[8];
  if (w <= 0) return [-1, -1];
  return [(m[0] * x + m[1] * y + m[2]) / w, (m[3] * x + m[4] * y + m[5]) / w];
}

const quadArea = q => Math.abs(q.reduce((s, [x, y], i) => s + x * q[(i + 1) % 4][1] - q[(i + 1) % 4][0] * y, 0)) / 2;

function refOp(r, layer, opacity) {
  const m = quadInverse(r);
  const W = doc.width;
  const H = doc.height;
  return {
    layer,
    xf: new Float32Array([m[0] * W, m[3] * W, m[6] * W, m[1] * H, m[4] * H, m[7] * H, m[2], m[5], m[8]]),
    px: Math.sqrt(quadArea(r.quad) / (layer.w * layer.h)),
    opacity,
  };
}

const maskFor = f => (stroke?.frame === f ? { color: rgba(stroke.color), erase: stroke.erase } : null);

// Back to front: paper, references (the lowest first), own reference, onion ghosts (the far ones first), the drawing
// with the stroke in progress. While the own reference is being drawn it comes forward at full strength and the
// animation steps back.
function sceneOps({ paper = true, reference = true, sketch = true, ghosts = true, drawing = true, refOpacity = null } = {}) {
  const ops = [];
  const editing = editSketch && !playing;
  if (paper) ops.push({ color: rgba(doc.paper) });
  if (reference) for (const r of refs) if (r.visible && r.layer) ops.push(refOp(r, r.layer, refOpacity ?? r.opacity));
  const sk = doc.sketch;
  if (sketch && sk.layer && (sk.visible || editing)) ops.push({ layer: sk.layer, opacity: editing ? 1 : sk.opacity, mask: maskFor(sk) });
  const o = prefs.onion;
  if (ghosts && o.on && !playing && !editing) {
    // A light table: red behind, green ahead, fading with distance.
    const ghost = (i, color, k) => {
      const f = doc.frames[i];
      if (f?.layer) ops.push({ layer: f.layer, tint: [...rgb(color), 0.85], opacity: o.opacity * 0.6 ** (k - 1) });
    };
    for (let k = o.prev; k >= 1; k--) ghost(cur - k, o.prevColor, k);
    for (let k = o.next; k >= 1; k--) ghost(cur + k, o.nextColor, k);
  }
  const f = doc.frames[cur];
  if (drawing && f.layer) ops.push({ layer: f.layer, opacity: editing ? 0.35 : 1, mask: maskFor(f) });
  return ops;
}

function render() {
  renderQueued = false;
  if (!doc || gpu.lost) return;
  const t = performance.now();
  if (t - renderAsked > 300) stall(`frame came ${Math.round(t - renderAsked)} ms after it was asked for`);
  const d = dpr();
  const w = Math.round(stage.clientWidth * d);
  const h = Math.round(stage.clientHeight * d);
  if (glCanvas.width !== w || glCanvas.height !== h) {
    glCanvas.width = w;
    glCanvas.height = h;
  }
  const place = { x: view.x * d, y: view.y * d, w: doc.width * view.zoom, h: doc.height * view.zoom, mirror: view.mirror };
  gpu.draw(null, place, doc.width, sceneOps());
  const ms = performance.now() - t;
  perf.renders++;
  perf.renderMs += ms;
  perf.renderMax = Math.max(perf.renderMax, ms);
}

// Renders part of the scene offscreen and reads it back as premultiplied RGBA, rows top-down: a w x h window of
// the document at 1:1 starting at x, y, or with fit the whole document scaled into w x h.
function renderDoc(name, w, h, ops, { x = 0, y = 0, fit = false } = {}) {
  const target = gpu.scratchLayer(name, w, h);
  const place = fit ? { x: 0, y: 0, w, h } : { x: -x, y: -y, w: doc.width, h: doc.height };
  gpu.draw(target, place, doc.width, ops);
  return gpu.read(target);
}

async function contextRestored() {
  // Everything on the GPU is gone. Drawings come back from their last saved or autosaved PNG.
  undoStack.length = 0;
  redoStack.length = 0;
  let lost = 0;
  for (const f of [...doc.frames, doc.sketch]) {
    const had = f.rev > 0 || !!f.layer;
    f.layer = null;
    if (f.saved) await uploadPng(f, f.saved.png, doc.width, doc.height);
    if (had && f.saved?.rev !== f.rev) lost++;
    if (f.layer) scheduleThumb(f);
  }
  for (const r of refs) {
    if (r.kind === 'image') uploadImage(r);
    else {
      r.layer = gpu.layer(r.size.w, r.size.h);
      r.shownTick = null;
    }
  }
  showFrame(cur);
  const text = lost ? `Відеокарта перезапустилася: ${nFrames(lost)} повернуто до останнього автозбереження` : 'Відеокарта перезапустилася, усе відновлено';
  toast(text, !!lost);
}

// ---------- showing a frame ----------

function showFrame(i, scroll = true) {
  cur = clamp(i, 0, doc.frames.length - 1);
  syncReference();
  markCells(scroll);
  updateInfo();
  requestRender();
}

function updateInfo() {
  const t = ticks[cur];
  const sec = t / doc.fps;
  const time = `${Math.floor(sec / 60)}:${(sec % 60).toFixed(2).padStart(5, '0')}`;
  $('#frameInfo').innerHTML = `Кадр <b>${cur + 1}</b> / ${doc.frames.length} · ${time}`;
  hud.innerHTML = `<b>${cur + 1}</b> / ${doc.frames.length}`;
  const f = doc.frames[cur];
  $('#holdVal').textContent = `×${f.hold}`;
  $('#holdMinus').disabled = f.hold <= 1;
  $('#docMeta').textContent = `${doc.width}×${doc.height} · ${fmtFps(doc.fps)} к/с · ${nFrames(doc.frames.length)}, ${(totalTicks() / doc.fps).toFixed(2)} с`;
}

// ---------- timeline strip ----------

function buildStrip() {
  const frag = document.createDocumentFragment();
  doc.frames.forEach((f, i) => {
    const cell = document.createElement('div');
    cell.className = 'cell';
    cell.dataset.i = i;
    const col = document.createElement('div');
    col.className = 'col';
    const thumb = document.createElement('div');
    thumb.className = 'thumb';
    thumb.style.background = doc.paper;
    if (f.thumb) thumb.append(f.thumb);
    const num = document.createElement('span');
    num.className = 'num';
    num.textContent = i + 1;
    col.append(thumb, num);
    cell.append(col);
    if (f.hold > 1) {
      const tail = document.createElement('div');
      tail.className = 'tail';
      tail.style.width = `${(f.hold - 1) * HOLD_W}px`;
      tail.textContent = `×${f.hold}`;
      cell.append(tail);
    }
    frag.append(cell);
  });
  strip.replaceChildren(frag);
  markCells(true);
}

let markedCell = null;
function markCells(scroll) {
  markedCell?.classList.remove('cur');
  markedCell = strip.children[cur] || null;
  if (!markedCell) return;
  markedCell.classList.add('cur');
  if (scroll) {
    const a = markedCell.offsetLeft;
    const b = a + markedCell.offsetWidth;
    if (a < strip.scrollLeft + 10) strip.scrollLeft = a - 40;
    else if (b > strip.scrollLeft + strip.clientWidth - 10) strip.scrollLeft = b - strip.clientWidth + 40;
  }
}

const thumbQueue = new Set();
let thumbTimer = 0;
function scheduleThumb(f) {
  if (f === doc.sketch) return; // not on the timeline
  thumbQueue.add(f);
  clearTimeout(thumbTimer);
  thumbTimer = setTimeout(flushThumbs, 150);
}

// Thumbnails are rendered on the GPU (mipmapped, so thin lines survive the shrink) and read back small.
function flushThumbs() {
  const w = Math.round(clamp((40 * doc.width) / doc.height, 24, 96) * 2);
  const h = 80;
  for (const f of thumbQueue) {
    if (!f.layer || gpu.lost) continue;
    if (!f.thumb || f.thumb.width !== w) f.thumb = Object.assign(document.createElement('canvas'), { width: w, height: h });
    const px = renderDoc('thumb', w, h, [{ color: rgba(doc.paper) }, { layer: f.layer }], { fit: true });
    f.thumb.getContext('2d').putImageData(new ImageData(new Uint8ClampedArray(px.buffer), w, h), 0, 0);
    const i = doc.frames.indexOf(f);
    const box = strip.children[i]?.querySelector('.thumb');
    if (box && f.thumb.parentNode !== box) box.replaceChildren(f.thumb);
  }
  thumbQueue.clear();
}

let stripDrag = null;
strip.addEventListener('pointerdown', e => {
  const cell = e.target.closest('.cell');
  if (!cell || e.button !== 0) return;
  stopPlayback();
  const i = +cell.dataset.i;
  showFrame(i, false);
  stripDrag = { i, x: e.clientX, on: false, to: i };
  strip.setPointerCapture(e.pointerId);
});
strip.addEventListener('pointermove', e => {
  if (!stripDrag) return;
  if (!stripDrag.on && Math.abs(e.clientX - stripDrag.x) < 6) return;
  stripDrag.on = true;
  strip.children[stripDrag.i]?.classList.add('dragging');
  const cells = [...strip.querySelectorAll('.cell')];
  let to = cells.length;
  for (let k = 0; k < cells.length; k++) {
    const r = cells[k].getBoundingClientRect();
    if (e.clientX < r.left + r.width / 2) {
      to = k;
      break;
    }
  }
  stripDrag.to = to;
  let mark = $('#dropMark');
  if (!mark) {
    mark = Object.assign(document.createElement('div'), { id: 'dropMark' });
    strip.append(mark);
  }
  const ref = cells[to] || cells[cells.length - 1];
  mark.style.left = `${to < cells.length ? ref.offsetLeft - 3 : ref.offsetLeft + ref.offsetWidth + 1}px`;
});
const endStripDrag = () => {
  if (!stripDrag) return;
  const { i, to, on } = stripDrag;
  stripDrag = null;
  $('#dropMark')?.remove();
  strip.querySelector('.dragging')?.classList.remove('dragging');
  if (on) moveFrame(i, to > i ? to - 1 : to);
};
strip.addEventListener('pointerup', endStripDrag);
strip.addEventListener('pointercancel', endStripDrag);
strip.addEventListener('wheel', e => {
  if (Math.abs(e.deltaY) > Math.abs(e.deltaX)) {
    strip.scrollLeft += e.deltaY;
    e.preventDefault();
  }
}, { passive: false });

// ---------- undo ----------

const undoStack = [];
const redoStack = [];

const dropEntry = e => e.type === 'pixels' && gpu.free(e.data);

function pushUndo(entry) {
  undoStack.push(entry);
  if (undoStack.length > UNDO_LIMIT) dropEntry(undoStack.shift());
  redoStack.forEach(dropEntry);
  redoStack.length = 0;
  changed();
}

// Pixel entries keep the changed rectangle as a small texture and swap it with what is on the frame now,
// so undo and redo are the same move and never leave the GPU.
function swapPixels(e) {
  const layer = ensureLayer(e.frame);
  const now = gpu.copyOut(layer, e.r);
  gpu.copyIn(layer, e.data, e.r);
  gpu.free(e.data);
  e.data = now;
  e.frame.rev++;
  scheduleThumb(e.frame);
  if (e.frame === doc.sketch) {
    doc.sketch.visible = true; // never change what cannot be seen
    showSketch();
    requestRender();
  }
  const i = doc.frames.indexOf(e.frame);
  if (i >= 0) showFrame(i);
}

const snap = () => ({ frames: doc.frames.map(f => [f, f.hold]), cur });

function restore(s) {
  doc.frames = s.frames.map(([f, hold]) => Object.assign(f, { hold }));
  recalc();
  buildStrip();
  showFrame(s.cur);
}

function undo() {
  const e = undoStack.pop();
  if (!e) return;
  stopPlayback();
  if (e.type === 'pixels') swapPixels(e);
  else if (e.type === 'xf') applyQuad(e.ref, e.before);
  else restore(e.before);
  redoStack.push(e);
  changed();
}

function redo() {
  const e = redoStack.pop();
  if (!e) return;
  stopPlayback();
  if (e.type === 'pixels') swapPixels(e);
  else if (e.type === 'xf') applyQuad(e.ref, e.after);
  else restore(e.after);
  undoStack.push(e);
  changed();
}

function structural(fn) {
  stopPlayback();
  const before = snap();
  fn();
  const after = snap();
  pushUndo({ type: 'struct', before, after });
  recalc();
  buildStrip();
  showFrame(cur);
}

function changed() {
  editRev++;
  setDirty(true);
  $('#undoBtn').disabled = !undoStack.length;
  $('#redoBtn').disabled = !redoStack.length;
}

// ---------- frame operations ----------

function addFrame() {
  structural(() => {
    doc.frames.splice(cur + 1, 0, makeFrame(prefs.step));
    cur++;
  });
}

function duplicateFrame() {
  const f = doc.frames[cur];
  const copy = makeFrame(f.hold);
  if (f.layer) {
    copy.layer = gpu.duplicate(f.layer);
    scheduleThumb(copy);
  }
  structural(() => {
    doc.frames.splice(cur + 1, 0, copy);
    cur++;
  });
}

function deleteFrame() {
  structural(() => {
    if (doc.frames.length === 1) doc.frames = [makeFrame(doc.frames[0].hold)];
    else doc.frames.splice(cur, 1);
    cur = Math.min(cur, doc.frames.length - 1);
  });
}

function moveFrame(from, to) {
  to = clamp(to, 0, doc.frames.length - 1);
  if (to === from) return;
  structural(() => {
    const [f] = doc.frames.splice(from, 1);
    doc.frames.splice(to, 0, f);
    cur = to;
  });
}

function changeHold(d) {
  const f = doc.frames[cur];
  const hold = clamp(f.hold + d, 1, 99);
  if (hold !== f.hold) structural(() => { f.hold = hold; });
}

// What the brush, Delete and the eyedropper's colour go to: the current frame, or the own reference.
const target = () => (editSketch ? doc.sketch : doc.frames[cur]);

function clearFrame(f = target()) {
  if (!f.layer) return;
  const r = { x: 0, y: 0, w: doc.width, h: doc.height };
  const data = gpu.copyOut(f.layer, r);
  gpu.clear(f.layer);
  f.rev++;
  pushUndo({ type: 'pixels', frame: f, r, data });
  scheduleThumb(f);
  if (f === doc.sketch) showSketch();
  showFrame(cur);
}

// Adds one drawing to another on the GPU, over it or under it (the own reference always goes under the frame,
// as it is shown); undo keeps the whole target.
function mergeInto(dst, src, under) {
  if (!src.layer) return false;
  const r = { x: 0, y: 0, w: doc.width, h: doc.height };
  ensureLayer(dst);
  const data = gpu.copyOut(dst.layer, r);
  const tmp = gpu.layer(doc.width, doc.height, { mips: false });
  const ops = [{ layer: dst.layer }, { layer: src.layer }];
  gpu.draw(tmp, r, doc.width, under ? ops.reverse() : ops);
  gpu.blit(tmp, dst.layer, r, r);
  gpu.free(tmp);
  dst.rev++;
  pushUndo({ type: 'pixels', frame: dst, r, data });
  scheduleThumb(dst);
  return true;
}

function frameToSketch() {
  stopPlayback();
  if (!mergeInto(doc.sketch, doc.frames[cur], false)) return toast('У кадрі нічого не намальовано');
  doc.sketch.visible = true;
  showSketch();
  requestRender();
  toast(`Малюнок кадру ${cur + 1} додано у свій референс`);
}

function sketchToFrame() {
  stopPlayback();
  if (!mergeInto(doc.frames[cur], doc.sketch, true)) return toast('Свій референс поки порожній');
  showFrame(cur);
  toast(`Свій референс додано в кадр ${cur + 1}`);
}

function go(i) {
  stopPlayback();
  showFrame(clamp(i, 0, doc.frames.length - 1));
}

// ---------- drawing ----------

let stroke = null;
let pan = null;
let hoverId = null; // the pointer the brush ring follows
const space = { down: false, used: false };

function pressureOf(ev) {
  if (ev.pointerType !== 'pen') return 1;
  return ev.pressure;
}

function feed(e) {
  const list = e.type === 'pointermove' && e.getCoalescedEvents ? e.getCoalescedEvents() : [];
  for (const ev of list.length ? list : [e]) {
    const [x, y] = toDoc(ev, stroke.rect);
    stroke.s.add(x, y, pressureOf(ev));
  }
}

function startStroke(e) {
  stopPlayback();
  const f = target();
  ensureLayer(f);
  gpu.beginStroke(doc.width, doc.height);
  const kind = e.button === 5 || e.buttons & 32 ? 'eraser' : prefs.tool;
  stroke = {
    frame: f,
    color: prefs.color,
    erase: kind === 'eraser',
    rect: sheet.getBoundingClientRect(),
    s: new Stroke(gpu, {
      kind,
      size: prefs.sizes[kind],
      angle: prefs.angle,
      smoothing: prefs.smoothing,
      pressure: prefs.pressure,
    }),
  };
  feed(e);
  stroke.s.flush();
  requestRender();
}

// The pen lifts: keep what was under the stroke for undo, then bake the stroke into the drawing.
function endStroke() {
  const { s, frame, color, erase } = stroke;
  s.end();
  stroke = null;
  const x = Math.max(0, Math.floor(s.box[0]));
  const y = Math.max(0, Math.floor(s.box[1]));
  const r = { x, y, w: Math.min(doc.width, Math.ceil(s.box[2])) - x, h: Math.min(doc.height, Math.ceil(s.box[3])) - y };
  if (r.w > 0 && r.h > 0) {
    const data = gpu.copyOut(frame.layer, r);
    gpu.commit(frame.layer, rgba(color), erase, r);
    frame.rev++;
    pushUndo({ type: 'pixels', frame, r, data });
    scheduleThumb(frame);
    if (frame === doc.sketch) showSketch();
  }
  requestRender();
}

function pickColor(e) {
  const [x, y] = toDoc(e, sheet.getBoundingClientRect());
  if (x < 0 || y < 0 || x >= doc.width || y >= doc.height) return;
  const [r, g, b] = renderDoc('pick', 1, 1, sceneOps({ ghosts: false }), { x: Math.floor(x), y: Math.floor(y) });
  setColor(`#${[r, g, b].map(v => v.toString(16).padStart(2, '0')).join('')}`);
  if (prefs.tool === 'eraser') setTool('round');
}

stage.addEventListener('pointerdown', e => {
  if (!doc || $('#modal').childElementCount || e.target.closest('#xfBadge')) return;
  moveCursor(e);
  if (e.button === 1 || (e.button === 0 && space.down)) {
    space.used = space.down;
    pan = { x: e.clientX, y: e.clientY, vx: view.x, vy: view.y };
    flag('panning', true, why(e));
  } else if (xform) {
    if (e.button !== 0 || !xfDown(e)) return;
  } else if (e.button === 0 || e.button === 5) {
    if (e.altKey) return pickColor(e);
    startStroke(e);
  } else {
    return;
  }
  stage.setPointerCapture(e.pointerId);
  e.preventDefault();
});

stage.addEventListener('pointermove', e => {
  moveCursor(e);
  if (stroke) {
    const t = performance.now();
    feed(e);
    stroke.s.flush();
    requestRender();
    const ms = performance.now() - t;
    perf.moves++;
    perf.ms += ms;
    perf.max = Math.max(perf.max, ms);
  } else if (drag) {
    xfMove(e);
  } else if (pan) {
    view.x = pan.vx + e.clientX - pan.x;
    view.y = pan.vy + e.clientY - pan.y;
    view.fitted = false;
    applyView();
  } else if (xform) {
    xfHover(e);
  }
});

const endPointer = e => {
  if (stroke) endStroke();
  if (drag) xfUp();
  if (pan) {
    pan = null;
    flag('panning', false, why(e));
  }
};
stage.addEventListener('pointerup', endPointer);
stage.addEventListener('pointercancel', endPointer);
stage.addEventListener('lostpointercapture', endPointer); // capture gone without a pointerup: nothing may stay stuck
// The brush ring follows whichever pointer last moved over the stage, and hides only when that one really goes off
// the stage. A tablet driver may move a mouse pointer alongside the pen; its leave must not take the pen's ring
// away. And a pen that drops out of range (a light touch, a pause; old tablets do it often) "leaves" from a spot
// over the sheet, sometimes with bogus coordinates: like the system cursor, the ring then stays where the pen was.
stage.addEventListener('pointerleave', e => {
  remember(e);
  if (e.pointerId !== hoverId) return;
  // What is really at that spot now: the sheet (the pen just went out of range), or a dialog, a panel, nothing.
  const over = stage.contains(document.elementFromPoint(e.clientX, e.clientY));
  if (over) af.log(`cursor: out kept (${why(e)} at ${Math.round(e.clientX)},${Math.round(e.clientY)}, still over the stage)`);
  else flag('out', true, why(e));
});
stage.addEventListener('pointerenter', remember);
stage.addEventListener('pointerover', moveCursor); // a pointer coming back shows the ring before it even moves
stage.addEventListener('contextmenu', e => e.preventDefault());

stage.addEventListener('wheel', e => {
  e.preventDefault();
  const r = stage.getBoundingClientRect();
  zoomAt(Math.exp(-e.deltaY * (e.deltaMode ? 0.05 : 0.0015)), e.clientX - r.left, e.clientY - r.top);
}, { passive: false });

function moveCursor(e) {
  hoverId = e.pointerId;
  flag('out', false, why(e));
  const r = stage.getBoundingClientRect();
  cursorEl.style.transform = `translate(${e.clientX - r.left}px, ${e.clientY - r.top}px)`;
}

// ---------- cursor: safety and diagnostics ----------
// Over the sheet the pen's point is marked twice: by a small system cross the OS draws (there even if the ring were
// lost) and by the ring that shows the brush size. Pen users still reported the cursor vanishing, so whatever
// changes how it looks goes to artframes.log with its cause, and F9 writes a full snapshot there, with the last
// pointer and key events, then puts the cursor back.

// The classes that change the cursor over the stage: out (the ring's pointer left), space (Space held: hand),
// panning (dragging the view).
function flag(name, on, cause) {
  if (stage.classList.contains(name) === on) return;
  stage.classList.toggle(name, on);
  af.log(`cursor: ${name} ${on ? 'on' : 'off'} (${cause}) stage="${stage.className}"`);
}

const why = e => (e ? `${e.type} ${e.pointerType}#${e.pointerId} buttons=${e.buttons}` : 'code');
const describe = el => (!el ? '-' : el.id ? `#${el.id}` : el.classList?.length ? `.${el.classList[0]}` : el.nodeName?.toLowerCase() || '?');

const trail = []; // the last 50 pointer, key and focus events; moves of one pointer over one element merge
let lastPointerType = null;
// Switches between pen and mouse. A Wacom driver interleaves mouse moves with the pen's several times a second, so
// the log gets the first switch and then a count at most every 10 s.
const switches = { n: 0, at: -Infinity };

function remember(e) {
  const t = Math.round(performance.now());
  const on = describe(e.target);
  if (e.pointerType && e.pointerType !== lastPointerType) {
    if (t - switches.at > 10000) {
      const more = switches.n ? `; ${switches.n} more switches since the last line` : '';
      af.log(`cursor: pointer type ${lastPointerType || '-'} -> ${e.pointerType}#${e.pointerId} (${e.type})${more}`);
      switches.n = 0;
      switches.at = t;
    } else {
      switches.n++;
    }
    lastPointerType = e.pointerType;
  }
  const last = trail[trail.length - 1];
  if (e.type === 'pointermove' && last?.ev === 'pointermove' && last.id === e.pointerId && last.on === on && last.b === e.buttons) {
    Object.assign(last, { t, x: Math.round(e.clientX), y: Math.round(e.clientY), n: last.n + 1 });
    return;
  }
  trail.push(e.pointerId === undefined
    ? { t, ev: e.type, key: e.code, on }
    : { t, ev: e.type, pt: e.pointerType, id: e.pointerId, b: e.buttons, btn: e.button, x: Math.round(e.clientX), y: Math.round(e.clientY), on, n: 1 });
  if (trail.length > 50) trail.shift();
}
for (const type of ['pointerdown', 'pointerup', 'pointermove', 'pointercancel', 'pointerover', 'pointerout', 'gotpointercapture', 'lostpointercapture', 'keydown', 'keyup', 'blur', 'focus']) {
  addEventListener(type, remember, { capture: true, passive: true });
}
document.addEventListener('visibilitychange', () => remember({ type: `visibility-${document.visibilityState}` }));

// Raw pointer updates arrive as soon as the OS hands them over, not once per frame like pointermove; counting them
// shows whether the pen still talks to the app while the moves (and frames) have stopped.
const raw = { n: 0, t: 0, pt: null, id: null, x: 0, y: 0 };
addEventListener('pointerrawupdate', e => {
  Object.assign(raw, { n: raw.n + 1, t: Math.round(performance.now()), pt: e.pointerType, id: e.pointerId, x: Math.round(e.clientX), y: Math.round(e.clientY) });
}, { passive: true });

// Stalls: the main thread (a timer firing late) or a frame that was asked for and came late. Some pen setups make
// an app freeze until the mouse moves; these lines tell that apart from the cursor logic.
let lastStall = 0;
function stall(what) {
  const now = performance.now();
  if (now - lastStall < 3000 || document.visibilityState !== 'visible') return;
  lastStall = now;
  const last = trail[trail.length - 1];
  af.log(`cursor: stall, ${what}; last event ${last ? `${last.ev} ${last.pt || last.key || ''}#${last.id ?? ''} ${Math.round(now - last.t)} ms ago` : '-'}; raw updates ${raw.n}, last ${raw.t ? Math.round(now - raw.t) : '-'} ms ago`);
}
let beat = performance.now();
setInterval(() => {
  const now = performance.now();
  if (now - beat > 900) stall(`main thread was busy ${Math.round(now - beat - 500)} ms`);
  beat = now;
}, 500);

function cursorSnapshot() {
  const c = getComputedStyle(cursorEl);
  const ring = cursorEl.firstElementChild.getBoundingClientRect();
  const at = /translate\(([-\d.]+)px, ([-\d.]+)px\)/.exec(cursorEl.style.transform);
  const last = [...trail].reverse().find(t => t.x !== undefined);
  const s = {
    stage: stage.className || '-', systemCursor: getComputedStyle(stage).cursor.slice(0, 32),
    ring: { display: c.display, opacity: c.opacity, kind: cursorEl.className || '-', at: at ? [+at[1], +at[2]] : null, size: [Math.round(ring.width), Math.round(ring.height)] },
    stageSize: [stage.clientWidth, stage.clientHeight], hoverId, stroke: !!stroke, pan: !!pan, space: { ...space },
    focus: document.hasFocus(), visibility: document.visibilityState, active: describe(document.activeElement), modal: $('#modal').childElementCount > 0,
    under: last ? describe(document.elementFromPoint(last.x, last.y)) : '-',
    tool: prefs.tool, size: prefs.sizes[prefs.tool], zoom: +view.zoom.toFixed(3), dpr: dpr(), editSketch, xform, playing: !!playing,
    now: Math.round(performance.now()), raw: { ...raw }, trail,
  };
  af.log(`cursor snapshot ${JSON.stringify(s)}`);
}

// F9 ("the cursor is gone"): the snapshot first, then everything that can hide or change the cursor is reset.
function cursorRescue() {
  cursorSnapshot();
  if (!stroke) {
    space.down = false;
    pan = null;
    flag('space', false, 'F9');
    flag('panning', false, 'F9');
  }
  flag('out', false, 'F9');
  shapeCursor();
  toast('Стан курсора записано в журнал, курсор повернуто');
}

// The cross: white with a dark edge, so it shows on paper and on video alike, with a dot at the very point.
function crossCursor() {
  const image = scale => {
    const c = Object.assign(document.createElement('canvas'), { width: 13 * scale, height: 13 * scale });
    const g = c.getContext('2d');
    g.scale(scale, scale);
    const arms = () => {
      g.beginPath();
      for (const [x0, y0, x1, y1] of [[6.5, 0.5, 6.5, 4.5], [6.5, 8.5, 6.5, 12.5], [0.5, 6.5, 4.5, 6.5], [8.5, 6.5, 12.5, 6.5]]) {
        g.moveTo(x0, y0);
        g.lineTo(x1, y1);
      }
      g.stroke();
    };
    g.strokeStyle = 'rgba(0, 0, 0, .7)';
    g.lineWidth = 3;
    arms();
    g.fillStyle = 'rgba(0, 0, 0, .7)';
    g.fillRect(5, 5, 3, 3);
    g.strokeStyle = g.fillStyle = '#fff';
    g.lineWidth = 1;
    arms();
    g.fillRect(6, 6, 1, 1);
    return `url(${c.toDataURL()})`;
  };
  const sharp = `image-set(${image(1)} 1x, ${image(2)} 2x) 6 6, crosshair`;
  const style = document.createElement('style');
  style.textContent = `#stage { cursor: ${CSS.supports('cursor', sharp) ? sharp : `${image(1)} 6 6, crosshair`}; }`;
  document.head.append(style);
}
crossCursor();

function shapeCursor() {
  if (!doc) return;
  const tool = prefs.tool;
  const d = prefs.sizes[tool] * cssScale();
  const i = cursorEl.firstElementChild;
  cursorEl.className = tool === 'flat' ? 'flat' : '';
  if (d < 4) cursorEl.classList.add('tiny');
  if (tool === 'flat') {
    i.style.width = `${d}px`;
    i.style.height = `${Math.max(2, d * 0.16)}px`;
    i.style.transform = `translate(-50%, -50%) rotate(${view.mirror ? prefs.angle : -prefs.angle}deg)`;
  } else {
    i.style.width = i.style.height = `${d}px`;
    i.style.transform = 'translate(-50%, -50%)';
  }
}

// ---------- tools, colour, size ----------

const SIZE_MIN = 1;
const SIZE_MAX = 400;
const sizeToRange = s => Math.round((Math.log(s / SIZE_MIN) / Math.log(SIZE_MAX / SIZE_MIN)) * 1000);
const rangeToSize = v => Math.round(SIZE_MIN * (SIZE_MAX / SIZE_MIN) ** (v / 1000));

function setTool(tool) {
  prefs.tool = tool;
  $$('#tools button').forEach(b => b.classList.toggle('on', b.dataset.tool === tool));
  $('#angleRow').style.opacity = tool === 'flat' ? 1 : 0.5;
  showSize();
  savePrefs();
}

function setSize(size) {
  prefs.sizes[prefs.tool] = clamp(Math.round(size), SIZE_MIN, SIZE_MAX);
  showSize();
  savePrefs();
}

function showSize() {
  const s = prefs.sizes[prefs.tool];
  $('#sizeRange').value = sizeToRange(s);
  if (document.activeElement !== $('#sizeNum')) $('#sizeNum').value = s;
  shapeCursor();
}

function setColor(color) {
  prefs.color = color;
  $$('#colors button').forEach(b => b.classList.toggle('on', b.dataset.color === color));
  const custom = !PALETTE.includes(color);
  $('.swatch-pick').classList.toggle('custom', custom);
  $('.swatch-pick').style.setProperty('--c', color);
  $('#colorPick').value = color;
  if (prefs.tool === 'eraser') setTool('round');
  savePrefs();
}

// ---------- reference ----------

const videos = () => refs.filter(r => r.kind === 'video');

// Each decoded video frame goes straight into its reference texture.
function drawRefFrame(r, canvas) {
  if (!canvas || !r.layer || gpu.lost || canvas.width !== r.layer.w || canvas.height !== r.layer.h) return;
  gpu.upload(r.layer, canvas);
  requestRender();
}

// Where a picture or video sits before it is transformed: contain-fit into the sheet, centred.
function fitRect(w0, h0) {
  const s = Math.min(doc.width / w0, doc.height / h0);
  const w = Math.round(w0 * s);
  const h = Math.round(h0 * s);
  return { x: Math.round((doc.width - w) / 2), y: Math.round((doc.height - h) / 2), w, h };
}

const rectQuad = ({ x, y, w, h }) => [[x, y], [x + w, y], [x + w, y + h], [x, y + h]];

// A picture is uploaded once at its own resolution (so scaling it up stays sharp), smaller only if it is bigger than
// the GPU takes.
function uploadImage(r) {
  const k = Math.min(1, Math.min(gpu.maxSize, 8192) / Math.max(r.width, r.height));
  const c = Object.assign(document.createElement('canvas'), { width: Math.round(r.width * k), height: Math.round(r.height * k) });
  c.getContext('2d').drawImage(r.bitmap, 0, 0, c.width, c.height);
  gpu.free(r.layer);
  r.layer = gpu.layer(c.width, c.height);
  gpu.upload(r.layer, c);
  requestRender();
}

// The video texture is the size frames are decoded at: the area on the sheet, more when the video is scaled up
// (up to its own resolution).
function layoutVideo(r, offset = r.offset, k = r.decodeK || 1) {
  r.layout(doc.width, doc.height, doc.fps, offset, k);
  r.decodeK = k;
  gpu.free(r.layer);
  r.layer = gpu.layer(r.size.w, r.size.h);
}

function fitDecode(r) {
  if (r.kind !== 'video') return;
  const s = Math.sqrt(quadArea(r.quad) / (r.rect.w * r.rect.h));
  const most = Math.max(1, Math.min(r.width / r.rect.w, Math.min(gpu.maxSize, 4096) / Math.max(r.rect.w, r.rect.h)));
  const k = clamp(s, 1, most);
  const now = r.decodeK || 1;
  if (Math.abs(k - now) / now < 0.15) return;
  layoutVideo(r, r.offset, k);
  syncReference();
}

function syncReference() {
  requestRender();
  if (playing) return;
  const ahead = [];
  for (let k = 1; k <= 4 && cur + k < doc.frames.length; k++) ahead.push(ticks[cur + k]);
  if (cur > 0) ahead.push(ticks[cur - 1]);
  for (const r of videos()) {
    r.show(ticks[cur]);
    r.prefetch(ahead);
  }
}

// One audio element: it plays the video whose sound is on (at most one has it).
const soundRef = () => videos().find(r => r.sound && r.hasAudio) || null;

async function updateAudio() {
  const file = soundRef()?.file || '';
  if (audio.dataset.file === file) return;
  audio.dataset.file = file;
  if (file) audio.src = await af.fileURL(file);
  else {
    audio.removeAttribute('src');
    audio.load();
  }
}

const validQuad = q => Array.isArray(q) && q.length === 4 && q.every(p => Array.isArray(p) && p.length === 2 && p.every(Number.isFinite));

let nextRefId = 1;

// Adds a picture or a video as a new reference layer on top of the others.
async function loadReference(file, o = {}) {
  const ext = file.split('.').pop().toLowerCase();
  if (!VIDEO_EXT.has(ext) && !IMAGE_EXT.has(ext)) throw new Error('Підтримуються картинки (PNG, JPG, WebP) і відео (MP4, MOV, WebM, MKV)');
  stopPlayback();
  let r;
  if (VIDEO_EXT.has(ext)) {
    const video = await openVideo(file);
    let note = '';
    if (pristine() && !refs.length && o.adopt !== false) {
      // Nothing drawn yet: the project takes the video's size and frame rate and stretches over the whole clip.
      const width = video.width - (video.width % 2);
      const height = video.height - (video.height % 2);
      setDoc({ width, height, fps: video.fps, paper: doc.paper });
      note = `Проєкт підлаштовано під відео: ${width}×${height}, ${fmtFps(video.fps)} к/с`;
    }
    r = Object.assign(video, {
      id: nextRefId++,
      name: basename(file),
      opacity: o.opacity ?? 1,
      visible: o.visible ?? true,
      sound: o.sound ?? !videos().some(v => v.sound),
    });
    video.onFrame = canvas => drawRefFrame(r, canvas);
    refs.push(r);
    layoutVideo(r, o.offset || 0, 1);
    r.quad = validQuad(o.quad) ? o.quad : rectQuad(r.rect);
    fitDecode(r);
    await updateAudio();
    if (note) {
      const total = video.ticks();
      const frames = [];
      for (let t = 0; t < total; t += prefs.step) frames.push(makeFrame(Math.min(prefs.step, total - t)));
      doc.frames = frames;
      recalc();
      buildStrip();
      note += `, ${nFrames(doc.frames.length)}`;
    }
    showFrame(note ? 0 : cur);
    if (note) toast(note);
  } else {
    const bytes = o.bytes || (await af.read(file));
    const bitmap = await createImageBitmap(new Blob([bytes]));
    r = { id: nextRefId++, kind: 'image', file, name: basename(file), bytes, bitmap, width: bitmap.width, height: bitmap.height, opacity: o.opacity ?? 0.5, visible: o.visible ?? true };
    refs.push(r);
    r.rect = fitRect(r.width, r.height);
    r.quad = validQuad(o.quad) ? o.quad : rectQuad(r.rect);
    uploadImage(r);
    syncReference();
  }
  if (o.select !== false) sel = r;
  if (!o.quiet) changed();
  refreshUI();
  drawXform();
  return r;
}

function removeReference(r = sel, quiet = false) {
  const i = refs.indexOf(r);
  if (i < 0) return;
  stopPlayback();
  if (r.kind === 'video') r.dispose();
  else r.bitmap?.close();
  gpu.free(r.layer);
  r.layer = null;
  refs.splice(i, 1);
  // Its transforms leave the undo history with it.
  for (const stack of [undoStack, redoStack]) for (let k = stack.length - 1; k >= 0; k--) if (stack[k].ref === r) stack.splice(k, 1);
  if (sel === r) sel = refs[Math.min(i, refs.length - 1)] || null;
  if (!refs.length) setXform(false);
  updateAudio();
  requestRender();
  drawXform();
  if (!quiet) {
    changed();
    refreshUI();
  }
}

function removeAllReferences() {
  for (const r of [...refs]) removeReference(r, true);
}

function relayoutVideo() {
  for (const r of videos()) layoutVideo(r);
  syncReference();
}

function fillToVideo() {
  const v = sel?.kind === 'video' ? sel : videos()[0];
  if (!v) return;
  const need = v.ticks();
  if (totalTicks() >= need) return toast('Таймлайн уже покриває все відео');
  structural(() => {
    let t = totalTicks();
    while (t < need) {
      const f = makeFrame(Math.min(prefs.step, need - t));
      doc.frames.push(f);
      t += f.hold;
    }
  });
  toast(`Тепер ${nFrames(doc.frames.length)}`);
}

async function pickReference() {
  const file = await af.openDialog('reference');
  if (file) await guarded(() => loadReference(file));
}

// Ctrl+V: a picture on the clipboard (a screenshot, a frame copied from a player, ArtNote's PNG) becomes the
// reference just like an opened picture and travels inside the project; a picture or video file copied in Explorer
// opens from where it is. In number fields Ctrl+V stays an ordinary paste.
document.addEventListener('paste', e => {
  if (!doc || typing(e.target) || $('#modal').childElementCount) return;
  e.preventDefault();
  guarded(() => pasteReference(e.clipboardData));
});

async function pasteReference(data) {
  const supported = name => {
    const ext = name.split('.').pop().toLowerCase();
    return VIDEO_EXT.has(ext) || IMAGE_EXT.has(ext);
  };
  const files = [...(data?.files || [])];
  const copied = files.map(f => af.pathForFile(f)).find(p => p && supported(p));
  if (copied) {
    await loadReference(copied);
    return toast(`Референс із буфера: ${basename(copied)}`);
  }
  const image = files.find(f => f.type.startsWith('image/')) ||
    [...(data?.items || [])].find(i => i.kind === 'file' && i.type.startsWith('image/'))?.getAsFile();
  if (image) {
    const ext = { 'image/jpeg': 'jpg', 'image/png': 'png', 'image/webp': 'webp', 'image/gif': 'gif', 'image/bmp': 'bmp' }[image.type] || 'png';
    const name = `Вставлено ${new Date().toLocaleString('sv').replace(/:/g, '-')}.${ext}`;
    await loadReference(name, { bytes: new Uint8Array(await image.arrayBuffer()) });
    return toast('Референс вставлено з буфера');
  }
  // A path copied as text ("Copy as path" in Explorer puts it in quotes).
  const text = (data?.getData('text/plain') || '').trim().replace(/^"(.*)"$/, '$1');
  if (/^([a-z]:[\\/]|\\\\|\/)/i.test(text) && supported(text) && (await af.stat(text))) {
    await loadReference(text);
    return toast(`Референс із буфера: ${basename(text)}`);
  }
  toast('У буфері немає картинки: скопіюй картинку або файл картинки чи відео й натисни Ctrl+V');
}

// ---------- reference layers ----------

function selectRef(r) {
  if (!r || sel === r) return;
  sel = r;
  refreshRefs();
  drawXform();
}

function setRefVisible(r, v, quiet = false) {
  r.visible = v;
  if (playing && r.kind === 'video') {
    if (v) r.play(Math.floor(clock() * doc.fps), clock);
    else r.stop();
  }
  syncReference();
  drawXform();
  if (!quiet) {
    refreshRefs();
    changed();
  }
}

// R hides every reference that shows, and the next R brings the same ones back.
let hiddenByR = [];
function toggleRefs() {
  if (!refs.length) return;
  const shown = refs.filter(r => r.visible);
  if (shown.length) hiddenByR = shown;
  const back = hiddenByR.filter(r => refs.includes(r));
  for (const r of shown.length ? shown : back.length ? back : refs) setRefVisible(r, !shown.length, true);
  refreshRefs();
  changed();
}

// d = +1 one layer up (towards the drawings), -1 one down.
function moveRef(r, d) {
  const i = refs.indexOf(r);
  const j = i + d;
  if (i < 0 || j < 0 || j >= refs.length) return;
  refs.splice(i, 1);
  refs.splice(j, 0, r);
  refreshRefs();
  drawXform();
  requestRender();
  changed();
}

function setRefSound(r, on) {
  stopPlayback();
  for (const v of videos()) v.sound = v === r ? on : on ? false : v.sound;
  updateAudio();
  refreshRefs();
  changed();
}

// ---------- transform ----------
// T (or the frame button) puts the selected reference in a frame with handles. With the pen: drag inside to move,
// drag a corner to scale in proportion (Shift: freely, Alt: from the centre, Ctrl: that corner alone, for
// perspective), drag the knob above the frame or anywhere outside it to rotate (Shift: in 15° steps). A tap on
// another reference picks it. Every drag is one undo step. Corners are kept in document pixels.

let drag = null;

function setXform(v = !xform) {
  if (v === xform || stroke || drag) return;
  if (v && !refs.length) return toast('Спершу додай референс: Ctrl+I, Ctrl+V або перетягни файл у вікно');
  if (v) {
    stopPlayback();
    if (editSketch) setEditSketch(false);
    if (!sel) sel = refs[refs.length - 1];
    if (!sel.visible) setRefVisible(sel, true);
  }
  xform = v;
  flag('xform', v, v ? 'transform on' : 'transform off');
  document.body.classList.toggle('xforming', v);
  stage.dataset.zone = '';
  refreshRefs();
  drawXform();
}

const stageXY = e => {
  const r = stage.getBoundingClientRect();
  return [e.clientX - r.left, e.clientY - r.top];
};
const docXY = e => toDoc(e, sheet.getBoundingClientRect());
const onStage = ([x, y]) => [view.x + (view.mirror ? doc.width - x : x) * cssScale(), view.y + y * cssScale()];
const centre = q => [q.reduce((s, p) => s + p[0], 0) / 4, q.reduce((s, p) => s + p[1], 0) / 4];

function inside(r, [x, y]) {
  const [u, v] = uvAt(r, x, y);
  return u >= 0 && u <= 1 && v >= 0 && v <= 1;
}

// The frame on screen: corners, the middle of the top edge and the rotation knob 30 px beyond it.
function frameOf(q) {
  const s = q.map(onStage);
  const c = centre(s);
  const m = [(s[0][0] + s[1][0]) / 2, (s[0][1] + s[1][1]) / 2];
  const n = Math.hypot(m[0] - c[0], m[1] - c[1]) || 1;
  return { s, c, m, knob: [m[0] + ((m[0] - c[0]) / n) * 30, m[1] + ((m[1] - c[1]) / n) * 30] };
}

// What the pen is over: the knob, a corner (with the resize cursor that fits its direction), the selected
// reference, another one, or empty space around (rotates the selected one).
function zoneAt(e) {
  const p = stageXY(e);
  const d = docXY(e);
  const near = (a, radius) => Math.hypot(a[0] - p[0], a[1] - p[1]) <= radius;
  if (sel?.visible) {
    const { s, c, knob } = frameOf(sel.quad);
    if (near(knob, 14)) return { kind: 'rotate', cursor: 'rot' };
    for (let i = 0; i < 4; i++) {
      if (near(s[i], 13)) return { kind: 'corner', i, cursor: (s[i][0] - c[0]) * (s[i][1] - c[1]) > 0 ? 'nwse' : 'nesw' };
    }
    if (inside(sel, d)) return { kind: 'move', cursor: 'move' };
  }
  for (let i = refs.length - 1; i >= 0; i--) {
    if (refs[i] !== sel && refs[i].visible && inside(refs[i], d)) return { kind: 'move', ref: refs[i], cursor: 'move' };
  }
  return sel?.visible ? { kind: 'rotate', cursor: 'rot' } : null;
}

function xfHover(e) {
  stage.dataset.zone = zoneAt(e)?.cursor || '';
}

function xfDown(e) {
  const z = zoneAt(e);
  if (!z) return false;
  if (z.ref) selectRef(z.ref);
  drag = { r: sel, kind: z.kind, i: z.i, q0: sel.quad, p0: docXY(e), moved: false };
  stage.dataset.zone = z.cursor;
  return true;
}

function rotateQuad(q0, p0, p, snap) {
  const [cx, cy] = centre(q0);
  let a = Math.atan2(p[1] - cy, p[0] - cx) - Math.atan2(p0[1] - cy, p0[0] - cx);
  if (snap) {
    const top = Math.atan2(q0[1][1] - q0[0][1], q0[1][0] - q0[0][0]);
    const step = Math.PI / 12;
    a = Math.round((top + a) / step) * step - top;
  }
  const c = Math.cos(a);
  const s = Math.sin(a);
  return q0.map(([x, y]) => [cx + (x - cx) * c - (y - cy) * s, cy + (x - cx) * s + (y - cy) * c]);
}

// Corner i follows the pen; the opposite corner (or the centre) stays put.
function scaleQuad(q0, i, p0, p, free, fromCentre) {
  const a = q0[(i + 2) % 4];
  const o = fromCentre ? centre(q0) : a;
  if (!free) {
    const vx = p0[0] - o[0];
    const vy = p0[1] - o[1];
    const k = ((p[0] - o[0]) * vx + (p[1] - o[1]) * vy) / (vx * vx + vy * vy || 1);
    if (k < 0.02) return null;
    return q0.map(([x, y]) => [o[0] + (x - o[0]) * k, o[1] + (y - o[1]) * k]);
  }
  // Freely: a separate stretch along each of the two edges that meet at the opposite corner.
  const e1 = [q0[(i + 3) % 4][0] - a[0], q0[(i + 3) % 4][1] - a[1]];
  const e2 = [q0[(i + 1) % 4][0] - a[0], q0[(i + 1) % 4][1] - a[1]];
  const det = e1[0] * e2[1] - e1[1] * e2[0];
  if (Math.abs(det) < 1e-6) return null;
  const along = ([x, y]) => {
    const X = x - o[0];
    const Y = y - o[1];
    return [(X * e2[1] - Y * e2[0]) / det, (e1[0] * Y - e1[1] * X) / det];
  };
  const [a0, b0] = along(p0);
  const [a1, b1] = along(p);
  const sa = Math.abs(a0) > 1e-6 ? a1 / a0 : 1;
  const sb = Math.abs(b0) > 1e-6 ? b1 / b0 : 1;
  if (sa < 0.02 || sb < 0.02) return null;
  return q0.map(c => {
    const [s, t] = along(c);
    return [o[0] + s * sa * e1[0] + t * sb * e2[0], o[1] + s * sa * e1[1] + t * sb * e2[1]];
  });
}

// A quad the picture can be drawn on: convex, no edge shorter than 2 px.
function sane(q) {
  let sign = 0;
  for (let k = 0; k < 4; k++) {
    const [ax, ay] = q[k];
    const [bx, by] = q[(k + 1) % 4];
    const [cx, cy] = q[(k + 2) % 4];
    const z = (bx - ax) * (cy - by) - (by - ay) * (cx - bx);
    if (Math.abs(z) < 1e-3 || Math.hypot(bx - ax, by - ay) < 2) return false;
    if (sign && Math.sign(z) !== sign) return false;
    sign = Math.sign(z);
  }
  return true;
}

function xfMove(e) {
  const { r, kind, i, q0, p0 } = drag;
  const p = docXY(e);
  const dx = p[0] - p0[0];
  const dy = p[1] - p0[1];
  if (!drag.moved && Math.hypot(dx, dy) * cssScale() < 2) return; // a tap is not a drag
  drag.moved = true;
  let q;
  if (kind === 'move') q = q0.map(([x, y]) => [x + dx, y + dy]);
  else if (kind === 'rotate') q = rotateQuad(q0, p0, p, e.shiftKey);
  else if (e.ctrlKey || e.metaKey) q = q0.map((c, k) => (k === i ? [c[0] + dx, c[1] + dy] : c));
  else q = scaleQuad(q0, i, p0, p, e.shiftKey, e.altKey);
  if (!q || !sane(q)) return;
  r.quad = q;
  requestRender();
  drawXform();
}

function xfUp() {
  const { r, q0, moved } = drag;
  drag = null;
  if (!moved || r.quad === q0) return;
  pushUndo({ type: 'xf', ref: r, before: q0, after: r.quad });
  fitDecode(r);
  drawXform();
}

// Undo and redo of a transform. Like any undo, it never changes what cannot be seen.
function applyQuad(r, q) {
  if (!refs.includes(r)) return;
  r.quad = q;
  sel = r;
  if (!r.visible) setRefVisible(r, true, true);
  fitDecode(r);
  refreshRefs();
  drawXform();
  requestRender();
}

function setQuad(r, q) {
  if (!r || JSON.stringify(q) === JSON.stringify(r.quad)) return;
  pushUndo({ type: 'xf', ref: r, before: r.quad, after: q });
  applyQuad(r, q);
}

// Mirrored left to right within its own frame: the corners swap places, the frame stays.
const flipRef = (r = sel) => r && setQuad(r, [r.quad[1], r.quad[0], r.quad[3], r.quad[2]]);
const resetRef = (r = sel) => r && setQuad(r, rectQuad(r.rect));

function drawXform() {
  const svg = $('#xfFrame');
  if (!doc || !xform) return svg.replaceChildren();
  const NS = 'http://www.w3.org/2000/svg';
  const el = (name, attrs) => {
    const n = document.createElementNS(NS, name);
    for (const k in attrs) n.setAttribute(k, attrs[k]);
    return n;
  };
  const points = q => q.map(onStage).map(([x, y]) => `${x.toFixed(1)},${y.toFixed(1)}`).join(' ');
  const parts = [];
  for (const r of refs) if (r !== sel && r.visible) parts.push(el('polygon', { points: points(r.quad), class: 'other' }));
  if (sel?.visible) {
    const { s, m, knob } = frameOf(sel.quad);
    parts.push(el('polygon', { points: points(sel.quad), class: 'shade' }), el('polygon', { points: points(sel.quad), class: 'frame' }));
    parts.push(el('line', { x1: m[0], y1: m[1], x2: knob[0], y2: knob[1], class: 'stick' }), el('circle', { cx: knob[0], cy: knob[1], r: 6, class: 'knob' }));
    for (const [x, y] of s) parts.push(el('rect', { x: x - 5, y: y - 5, width: 10, height: 10, class: 'handle' }));
  }
  svg.replaceChildren(...parts);
  $('#xfName').textContent = sel?.name || '';
}

// A round arrow for "rotate", drawn like the cross: white with a dark edge.
function rotateCursor() {
  const image = scale => {
    const c = Object.assign(document.createElement('canvas'), { width: 21 * scale, height: 21 * scale });
    const g = c.getContext('2d');
    g.scale(scale, scale);
    const a = Math.PI * 2.25;
    const [ex, ey] = [10.5 + 6.5 * Math.cos(a), 10.5 + 6.5 * Math.sin(a)];
    const [tx, ty, nx, ny] = [-Math.sin(a), Math.cos(a), Math.cos(a), Math.sin(a)];
    const shape = () => {
      g.beginPath();
      g.arc(10.5, 10.5, 6.5, Math.PI * 0.85, a - 0.25);
      g.stroke();
      g.beginPath();
      g.moveTo(ex + tx * 3.5, ey + ty * 3.5);
      g.lineTo(ex + nx * 3.5 - tx * 1.5, ey + ny * 3.5 - ty * 1.5);
      g.lineTo(ex - nx * 3.5 - tx * 1.5, ey - ny * 3.5 - ty * 1.5);
      g.closePath();
    };
    g.strokeStyle = g.fillStyle = 'rgba(0, 0, 0, .7)';
    g.lineWidth = 3.5;
    shape();
    g.stroke();
    g.strokeStyle = g.fillStyle = '#fff';
    g.lineWidth = 1.5;
    shape();
    g.fill();
    return `url(${c.toDataURL()})`;
  };
  const sharp = `image-set(${image(1)} 1x, ${image(2)} 2x) 10 10, alias`;
  const style = document.createElement('style');
  style.textContent = `#stage.xform[data-zone="rot"] { cursor: ${CSS.supports('cursor', sharp) ? sharp : `${image(1)} 10 10, alias`}; }`;
  document.head.append(style);
}
rotateCursor();

// ---------- own reference ----------

function setEditSketch(v = !editSketch) {
  if (stroke || drag || v === editSketch) return;
  stopPlayback();
  if (v) setXform(false);
  editSketch = v;
  if (v && !doc.sketch.visible) {
    doc.sketch.visible = true;
    changed();
  }
  showSketch();
  requestRender();
}

function toggleSketch(v = !doc.sketch.visible) {
  if (editSketch && !v) setEditSketch(false); // hidden means not being drawn
  doc.sketch.visible = v;
  showSketch();
  requestRender();
  changed();
}

function showSketch() {
  const sk = doc.sketch;
  document.body.classList.toggle('sketching', editSketch);
  $$('#target button').forEach(b => b.classList.toggle('on', (b.dataset.target === 'sketch') === editSketch));
  $('#sketchMode').classList.toggle('on', editSketch);
  $('#sketchMode').textContent = editSketch ? 'Готово, назад до кадрів' : 'Малювати свій референс';
  $('#sketchHint').hidden = !!sk.layer;
  $('#sketchVisible').checked = sk.visible;
  $('#sketchOpacity').value = Math.round(sk.opacity * 100);
  $('#sketchOpacityOut').textContent = `${Math.round(sk.opacity * 100)}%`;
  $('#sketchToFrame').disabled = !sk.layer;
  $('#sketchClear').disabled = !sk.layer;
}

// ---------- playback ----------

let playing = null;

const clock = () => (playing ? playing.from / doc.fps + (performance.now() - playing.t0) / 1000 : 0);

function play() {
  if (playing || !doc || drag) return;
  setXform(false);
  const from = cur >= doc.frames.length - 1 ? 0 : ticks[cur];
  playing = { t0: performance.now(), from, tick: -1 };
  requestRender();
  $('#playBtn').classList.add('on');
  $('#playBtn').innerHTML = '<svg viewBox="0 0 24 24"><path class="fill" d="M7 5.5h3.5v13H7zM13.5 5.5H17v13h-3.5z"/></svg>';
  startVideo(from);
  requestAnimationFrame(playLoop);
}

function startVideo(from) {
  for (const r of videos()) {
    if (r.visible) r.play(from, clock);
    if (from !== 0 && prefs.loop) r.prefetch([0]); // ready for the loop back to the start
  }
  const s = soundRef();
  if (s && audio.src) {
    audio.currentTime = Math.max(0, s.localTime(from));
    audio.play().catch(() => {});
  }
}

function playLoop() {
  if (!playing) return;
  let t = Math.floor(clock() * doc.fps + 1e-6);
  if (t >= totalTicks()) {
    if (!prefs.loop) {
      stopPlayback();
      return showFrame(doc.frames.length - 1);
    }
    playing.t0 = performance.now();
    playing.from = 0;
    t = 0;
    for (const r of videos()) r.stop();
    startVideo(0);
  }
  if (t !== playing.tick) {
    playing.tick = t;
    const i = frameAtTick(t);
    if (i !== cur || !playing.shown) {
      playing.shown = true;
      cur = i;
      requestRender();
      markCells(true);
      updateInfo();
    }
  }
  requestAnimationFrame(playLoop);
}

function stopPlayback() {
  if (!playing) return;
  playing = null;
  for (const r of videos()) r.stop();
  audio.pause();
  $('#playBtn').classList.remove('on');
  $('#playBtn').innerHTML = '<svg viewBox="0 0 24 24"><path class="fill" d="M8 5.5v13l10.5-6.5z"/></svg>';
  showFrame(cur);
}

const togglePlay = () => (playing ? stopPlayback() : play());

// ---------- project files ----------

function setDirty(v) {
  dirty = v;
  af.setState({ dirty, title: `${doc.name}${dirty ? ' •' : ''} — ArtFrames` });
}

// Premultiplied GPU pixels to the straight alpha PNG and ImageData expect.
function unpremultiply(px) {
  for (let i = 0; i < px.length; i += 4) {
    const a = px[i + 3];
    if (a === 0 || a === 255) continue;
    const k = 255 / a;
    px[i] = Math.min(255, Math.round(px[i] * k));
    px[i + 1] = Math.min(255, Math.round(px[i + 1] * k));
    px[i + 2] = Math.min(255, Math.round(px[i + 2] * k));
  }
  return px;
}

const pngCanvas = document.createElement('canvas');

async function pngBytes(layer) {
  const px = unpremultiply(gpu.read(layer));
  pngCanvas.width = layer.w;
  pngCanvas.height = layer.h;
  pngCanvas.getContext('2d').putImageData(new ImageData(new Uint8ClampedArray(px.buffer), layer.w, layer.h), 0, 0);
  const blob = await new Promise(r => pngCanvas.toBlob(r, 'image/png'));
  return new Uint8Array(await blob.arrayBuffer());
}

// Decoded through a 2D canvas so the upload is premultiplied the same way as everything drawn on the GPU.
async function uploadPng(f, png, w, h) {
  const bmp = await createImageBitmap(new Blob([png], { type: 'image/png' }));
  pngCanvas.width = w;
  pngCanvas.height = h;
  const ctx = pngCanvas.getContext('2d');
  ctx.clearRect(0, 0, w, h);
  ctx.drawImage(bmp, 0, 0);
  bmp.close();
  f.layer = gpu.layer(w, h);
  gpu.upload(f.layer, pngCanvas);
}

async function serialize() {
  const frames = [];
  for (const f of doc.frames) {
    if (f.layer && f.saved?.rev !== f.rev) f.saved = { rev: f.rev, png: await pngBytes(f.layer) };
    frames.push({ hold: f.hold, png: f.layer ? f.saved.png : null });
  }
  // Bottom first; pictures travel inside the project, videos by path.
  const references = refs.map(r => ({
    kind: r.kind,
    file: r.file,
    name: r.name,
    opacity: r.opacity,
    visible: r.visible,
    offset: r.offset || 0,
    sound: r.sound,
    quad: r.quad.map(([x, y]) => [Math.round(x * 1000) / 1000, Math.round(y * 1000) / 1000]),
    data: r.kind === 'image' ? r.bytes : null,
  }));
  const sk = doc.sketch;
  if (sk.layer && sk.saved?.rev !== sk.rev) sk.saved = { rev: sk.rev, png: await pngBytes(sk.layer) };
  return {
    meta: { width: doc.width, height: doc.height, fps: doc.fps, paper: doc.paper, cur, refSel: refs.indexOf(sel) },
    frames,
    refs: references,
    sketch: sk.layer ? { visible: sk.visible, opacity: sk.opacity, png: sk.saved.png } : null,
  };
}

async function applyProject(project, file) {
  const { meta, frames: stored, references = [] } = project;
  const frames = [];
  for (const s of stored) {
    const f = makeFrame(s.hold || 1);
    if (s.png) {
      await uploadPng(f, s.png, meta.width, meta.height);
      f.saved = { rev: 0, png: s.png };
    }
    frames.push(f);
  }
  const sketch = makeSketch();
  if (project.sketch) {
    await uploadPng(sketch, project.sketch.png, meta.width, meta.height);
    Object.assign(sketch, { visible: project.sketch.visible ?? true, opacity: project.sketch.opacity ?? 0.5, saved: { rev: 0, png: project.sketch.png } });
  }
  setDoc({ width: meta.width, height: meta.height, fps: meta.fps, paper: meta.paper, frames, sketch, file });
  const loaded = [];
  for (const reference of references) {
    const o = { ...reference, adopt: false, quiet: true, select: false, bytes: reference.data };
    try {
      if (reference.kind === 'video' && !(await af.stat(reference.file))) throw new Error(`Відео-референс не знайдено: ${reference.file}`);
      loaded.push(await loadReference(reference.file, o));
    } catch (err) {
      loaded.push(null);
      toast(err.message, true);
    }
  }
  selectRef(loaded[meta.refSel] || refs[refs.length - 1]);
  showFrame(meta.cur || 0);
  setDirty(false);
  autosavedRev = editRev;
}

async function save(as = false) {
  let file = doc.file;
  if (!file || as) {
    file = await af.saveDialog('project', `${stem(doc.name)}.artframes`);
    if (!file) return false;
  }
  toast('Зберігаю…');
  await af.saveProject(file, await serialize());
  doc.file = file;
  doc.name = basename(file);
  autosavedRev = editRev;
  setDirty(false);
  toast(`Збережено: ${doc.name}`);
  return true;
}

// Resolves to true when it is fine to throw the current document away.
async function confirmDiscard() {
  if (!dirty) return true;
  const answer = await modal({
    title: 'Зберегти зміни?',
    body: html(`<p>У «${esc(doc.name)}» є незбережені зміни.</p>`),
    buttons: [
      { label: 'Скасувати', value: 'cancel' },
      { label: 'Не зберігати', value: 'drop' },
      { label: 'Зберегти', value: 'save', primary: true },
    ],
  });
  if (answer === 'save') return save();
  return answer === 'drop';
}

async function openProject(file) {
  if (!file) file = await af.openDialog('project');
  if (!file || !(await confirmDiscard())) return;
  toast('Відкриваю…');
  await applyProject(await af.loadProject(file), file);
  toast(`Відкрито: ${basename(file)}`);
}

async function newProject() {
  if (!(await confirmDiscard())) return;
  const o = await newProjectDialog();
  if (!o) return;
  prefs.newDoc = o;
  savePrefs();
  setDoc({ ...o, paper: doc.paper });
  await af.autosaveClear();
}

setInterval(async () => {
  if (!doc || editRev === autosavedRev || stroke || playing) return;
  const rev = editRev;
  try {
    await af.autosave(await serialize());
    autosavedRev = rev;
  } catch (err) {
    af.log('autosave failed:', err.message);
  }
}, 60000);

af.onSaveAndClose(async () => {
  if (await save()) af.closeNow();
});
af.onOpenFile(file => guarded(() => openProject(file)));

// ---------- export ----------

async function exportDialog() {
  stopPlayback();
  // Over video the lowest visible video sets the length, the frame rate and the sound.
  const video = refs.find(r => r.kind === 'video' && r.visible) || null;
  const several = refs.filter(r => r.visible).length > 1;
  const st = {
    kind: prefs.exportKind || 'gif',
    scale: prefs.exportScale || 1,
    withRef: !!video,
    withSketch: false,
    transparent: false,
    audio: true,
  };
  const body = document.createElement('div');
  const render = () => {
    const vid = st.kind === 'mp4' || st.kind === 'webm';
    const overVideo = video && st.withRef;
    const n = overVideo ? video.ticks() : totalTicks();
    const len = `${(n / doc.fps).toFixed(2)} с${overVideo ? ' (уся довжина відео)' : ''}`;
    body.innerHTML = `
      <div class="row"><span>Формат</span><div class="choices" data-k="kind">
        <button data-v="gif">GIF</button><button data-v="mp4">MP4</button><button data-v="webm">WebM</button><button data-v="png">PNG-кадри</button>
      </div></div>
      <div class="row"><span>Розмір</span><div class="choices" data-k="scale">
        <button data-v="1">100%<small> ${doc.width}×${doc.height}</small></button><button data-v="0.5">50%</button><button data-v="0.25">25%</button>
      </div></div>
      ${refs.length ? `<label class="row toggle"><span>Підкласти ${refs.length > 1 ? 'референси' : 'референс'}</span><input type="checkbox" data-t="withRef"></label>` : ''}
      ${doc.sketch.layer ? `<label class="row toggle"><span>Підкласти свій референс</span><input type="checkbox" data-t="withSketch"></label>` : ''}
      ${overVideo && vid && video.hasAudio ? `<label class="row toggle"><span>Звук із відео</span><input type="checkbox" data-t="audio"></label>` : ''}
      ${st.kind === 'png' && !st.withRef ? `<label class="row toggle"><span>Прозорий фон</span><input type="checkbox" data-t="transparent"></label>` : ''}
      <p class="hint" style="margin-top:10px">${len} · ${fmtFps(overVideo && vid ? video.fps : doc.fps)} к/с${overVideo && vid ? ' (частота відео)' : ''}${st.kind === 'png' ? ` · ${n} PNG` : ''}.
      ${st.withRef && several ? 'Видимі референси підуть під малюнок на повну яскравість, так, як вони розставлені.' : overVideo ? 'Відео піде під малюнок на повну яскравість.' : ''}
      ${st.withSketch ? 'Свій референс ляже під кожен кадр на повну яскравість.' : ''}
      ${st.kind === 'gif' && st.scale === 1 && doc.width > 1000 ? 'Для GIF краще 50%: файл буде вчетверо легший.' : ''}</p>`;
    body.querySelectorAll('.choices').forEach(group => {
      const k = group.dataset.k;
      group.querySelectorAll('button').forEach(b => {
        const v = k === 'scale' ? +b.dataset.v : b.dataset.v;
        b.classList.toggle('on', st[k] === v);
        b.onclick = () => {
          st[k] = v;
          render();
        };
      });
    });
    body.querySelectorAll('[data-t]').forEach(input => {
      input.checked = st[input.dataset.t];
      input.onchange = () => {
        st[input.dataset.t] = input.checked;
        render();
      };
    });
  };
  render();
  const go = await modal({
    title: 'Експорт',
    body,
    buttons: [{ label: 'Скасувати', value: false }, { label: 'Експортувати', value: true, primary: true }],
  });
  if (!go) return;
  prefs.exportKind = st.kind;
  prefs.exportScale = st.scale;
  savePrefs();
  const name = stem(doc.name === 'Без назви' ? 'animation' : doc.name);
  const target = st.kind === 'png' ? await af.folderDialog() : await af.saveDialog(st.kind, `${name}.${st.kind}`);
  if (!target) return;
  await exportTo({ ...st, target, name });
}

// The exporter asks for finished pictures: paper, the visible references where they stand (pictures from their
// textures, video frames the exporter decoded itself), the own reference if asked for, the drawing, composited on the
// GPU at the export size and read back as RGBA rows.
function exportSource() {
  const shown = refs.filter(r => r.visible && r.layer);
  const shownVideos = shown.filter(r => r.kind === 'video');
  return {
    width: doc.width,
    height: doc.height,
    fps: doc.fps,
    frames: doc.frames,
    ticks,
    frameAtTick,
    video: shownVideos[0] || null,
    videos: shownVideos,
    unpremultiply,
    render(W, H, { frame, refs: withRefs = false, unders = null, paper = true, sketch = false }) {
      const ops = [];
      if (paper) ops.push({ color: rgba(doc.paper) });
      if (withRefs) {
        shown.forEach((r, i) => {
          if (r.kind === 'image') return ops.push(refOp(r, r.layer, 1));
          const c = unders?.get(r);
          if (!c) return;
          const u = gpu.scratchLayer(`under${i}`, c.width, c.height);
          gpu.upload(u, c);
          ops.push(refOp(r, u, 1));
        });
      }
      if (sketch && doc.sketch.layer) ops.push({ layer: doc.sketch.layer });
      if (frame?.layer) ops.push({ layer: frame.layer });
      return renderDoc('export', W, H, ops, { fit: true });
    },
  };
}

async function exportTo(job) {
  const bar = document.createElement('div');
  bar.innerHTML = '<p>Готую…</p><div class="progress"><i></i></div>';
  const cancel = { requested: false };
  const progress = p => {
    bar.querySelector('i').style.width = `${Math.round(p * 100)}%`;
    bar.querySelector('p').textContent = `Експорт… ${Math.round(p * 100)}%`;
  };
  const done = modal({
    title: `Експорт ${job.kind === 'png' ? 'PNG-кадрів' : job.kind.toUpperCase()}`,
    body: bar,
    buttons: [{ label: 'Скасувати', value: 'cancel' }],
  }).then(() => {
    cancel.requested = true;
    cancel.abort?.();
  });
  const t0 = performance.now();
  try {
    const result = await runExport(exportSource(), job, progress, cancel);
    closeModal();
    await done;
    if (result.cancelled) return toast('Експорт скасовано');
    const secs = ((performance.now() - t0) / 1000).toFixed(1);
    toast(`Готово за ${secs} с: ${basename(result.file)}${result.audioLost ? ' (звук не вдалося зберегти)' : ''}`, false, () => af.reveal(result.file));
    af.log(`export ${job.kind} -> ${result.file} in ${secs}s`);
    return result;
  } catch (err) {
    closeModal();
    await done;
    toast(`Експорт не вдався: ${err.message}`, true);
    af.log('export failed:', err.stack || err.message);
    throw err;
  }
}

// ---------- dialogs ----------

const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' })[c]);

function html(s) {
  const div = document.createElement('div');
  div.innerHTML = s;
  return div;
}

let modalResolve = null;

function modal({ title, body, buttons }) {
  closeModal();
  const box = $('#modal');
  const dialog = document.createElement('div');
  dialog.className = 'dialog';
  const h = document.createElement('h1');
  h.textContent = title;
  const row = document.createElement('div');
  row.className = 'buttons';
  dialog.append(h, body, row);
  box.replaceChildren(dialog);
  box.hidden = false;
  return new Promise(resolve => {
    modalResolve = resolve;
    for (const b of buttons) {
      const btn = document.createElement('button');
      btn.textContent = b.label;
      if (b.primary) btn.className = 'primary';
      btn.onclick = () => closeModal(b.value);
      row.append(btn);
    }
    modalResolve.buttons = buttons;
    setTimeout(() => (dialog.querySelector('input[type=number]') || row.lastChild)?.focus(), 30);
  });
}

function closeModal(value) {
  const resolve = modalResolve;
  modalResolve = null;
  $('#modal').hidden = true;
  $('#modal').replaceChildren();
  resolve?.(value);
}

const PRESETS = [
  [1920, 1080, 'Full HD'],
  [1280, 720, 'HD'],
  [3840, 2160, '4K'],
  [1080, 1080, 'квадрат'],
  [1080, 1920, 'вертикальне'],
];

async function newProjectDialog() {
  const st = { ...prefs.newDoc };
  const body = document.createElement('div');
  body.innerHTML = `
    <div class="row"><span>Розмір</span><div class="choices">${PRESETS.map(([w, h, n]) => `<button data-w="${w}" data-h="${h}">${n}<small> ${w}×${h}</small></button>`).join('')}</div></div>
    <div class="row"><span>Ширина × висота</span><input type="number" id="nw" min="64" max="8192"> × <input type="number" id="nh" min="64" max="8192"></div>
    <div class="row"><span>Кадрів на секунду</span><input type="number" id="nf" min="1" max="120"></div>
    <p class="hint">Класика — 24 к/с і новий кадр на двійках (×2). Якщо потім завантажиш відео в порожній проєкт, розмір і частота підлаштуються під нього самі.</p>`;
  const sync = () => {
    body.querySelector('#nw').value = st.width;
    body.querySelector('#nh').value = st.height;
    body.querySelector('#nf').value = st.fps;
    body.querySelectorAll('[data-w]').forEach(b => b.classList.toggle('on', +b.dataset.w === st.width && +b.dataset.h === st.height));
  };
  body.querySelectorAll('[data-w]').forEach(b => {
    b.onclick = () => {
      st.width = +b.dataset.w;
      st.height = +b.dataset.h;
      sync();
    };
  });
  body.addEventListener('input', () => {
    st.width = clamp(+body.querySelector('#nw').value || st.width, 64, 8192);
    st.height = clamp(+body.querySelector('#nh').value || st.height, 64, 8192);
    st.fps = clamp(+body.querySelector('#nf').value || st.fps, 1, 120);
    body.querySelectorAll('[data-w]').forEach(b => b.classList.toggle('on', +b.dataset.w === st.width && +b.dataset.h === st.height));
  });
  sync();
  const ok = await modal({ title: 'Новий проєкт', body, buttons: [{ label: 'Скасувати', value: false }, { label: 'Створити', value: true, primary: true }] });
  return ok ? { width: Math.round(st.width), height: Math.round(st.height), fps: st.fps } : null;
}

const KEYS = [
  ['B', 'кругла кисть'],
  ['F', 'широка кисть (товщина від напрямку)'],
  ['E', 'гумка · кінчик-гумка пера теж стирає'],
  ['[ ]', 'менша / більша кисть'],
  ['1 – 6', 'кольори палітри · Alt+клік — піпетка'],
  ['N', 'новий порожній кадр після поточного'],
  ['D', 'дублювати кадр'],
  ['Tab', 'малювати свій референс / назад до кадрів'],
  ['Delete', 'очистити кадр (у режимі референсу — референс) · Shift+Delete — видалити кадр'],
  ['← →  , .', 'попередній / наступний кадр · Home / End'],
  ['Alt+← →', 'пересунути кадр по таймлайну'],
  ['− =', 'утримання кадру: коротше / довше'],
  ['Пробіл', 'грати / пауза · затиснути й тягнути — рух полотна'],
  ['O', 'калька (onion skin)'],
  ['R', 'показати / сховати референси · Shift+R — свій референс · Ctrl+I — додати'],
  ['Ctrl+V', 'вставити референс з буфера новим шаром: картинку чи скопійований файл картинки або відео'],
  ['T', 'трансформувати референс: тягни — рух, кут — масштаб (Shift — вільно, Ctrl — перспектива, Alt — від центру), кружок над рамкою чи поза нею — поворот (Shift — по 15°), H — віддзеркалити, Enter / Esc — готово'],
  ['M', 'віддзеркалити полотно'],
  ['Колесо', 'масштаб · 0 — вмістити · середня кнопка — рух'],
  ['Ctrl+Z', 'скасувати · Ctrl+Shift+Z / Ctrl+Y — повторити'],
  ['Ctrl+S', 'зберегти · Ctrl+O відкрити · Ctrl+N новий'],
  ['Ctrl+E', 'експорт GIF / MP4 / WebM / PNG'],
  ['F9', 'курсор зник: повернути його й записати стан у журнал'],
];

function helpDialog() {
  const body = html(`<div class="keys">${KEYS.map(([k, t]) => `<div>${k.split(/\s+/).map(x => `<kbd>${esc(x)}</kbd>`).join('')}</div><span>${esc(t)}</span>`).join('')}</div>`);
  modal({ title: 'Гарячі клавіші', body, buttons: [{ label: 'Добре', value: true, primary: true }] });
}

let toastTimer = 0;
function toast(text, error = false, onClick = null) {
  const el = $('#toast');
  el.textContent = text;
  el.classList.toggle('err', error);
  el.classList.add('show');
  el.style.pointerEvents = onClick ? 'auto' : 'none';
  el.style.cursor = onClick ? 'pointer' : '';
  el.onclick = onClick;
  if (onClick) el.title = 'Показати в папці';
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => {
    el.classList.remove('show');
    el.style.pointerEvents = 'none'; // a faded toast must not keep catching the pen over the stage
  }, error ? 6000 : onClick ? 5000 : 2200);
}

async function guarded(fn) {
  try {
    return await fn();
  } catch (err) {
    toast(err.message || String(err), true);
    af.log('error:', err.stack || err.message);
    return null;
  }
}

// ---------- side panel and bar wiring ----------

function refreshUI() {
  if (!doc) return;
  setTool(prefs.tool);
  setColor(prefs.color);
  $('#pressure').checked = prefs.pressure;
  $('#smoothing').value = Math.round(prefs.smoothing * 100);
  $('#smoothingOut').textContent = `${Math.round(prefs.smoothing * 100)}%`;
  $('#angle').value = prefs.angle;
  $('#angleOut').textContent = `${prefs.angle}°`;
  const o = prefs.onion;
  $('#onionOn').checked = o.on;
  $('#onionBtn').classList.toggle('on', o.on);
  $$('.stepper').forEach(s => { s.querySelector('b').textContent = o[s.dataset.key]; });
  for (const k of ['prevColor', 'nextColor']) {
    $(`#${k}`).value = o[k];
    $(`#${k}`).nextElementSibling.style.setProperty('--c', o[k]);
  }
  $('#onionOpacity').value = Math.round(o.opacity * 100);
  $('#onionOpacityOut').textContent = `${Math.round(o.opacity * 100)}%`;
  $('#fps').value = Math.round(doc.fps * 1000) / 1000;
  $$('#stepSeg button').forEach(b => b.classList.toggle('on', +b.dataset.step === prefs.step));
  $('#loopBtn').classList.toggle('on', prefs.loop);
  $('#paperColor').value = doc.paper;
  $('#paperColor').nextElementSibling.style.setProperty('--c', doc.paper);
  refreshRefs();
  showSketch();
  $('#undoBtn').disabled = !undoStack.length;
  $('#redoBtn').disabled = !redoStack.length;
  updateInfo();
}

const ICONS = {
  eye: '<svg viewBox="0 0 24 24"><path d="M2.5 12s3.5-6.5 9.5-6.5 9.5 6.5 9.5 6.5-3.5 6.5-9.5 6.5S2.5 12 2.5 12z"/><circle cx="12" cy="12" r="2.6"/></svg>',
  hidden: '<svg viewBox="0 0 24 24"><path d="M2.5 12s3.5-6.5 9.5-6.5 9.5 6.5 9.5 6.5-3.5 6.5-9.5 6.5S2.5 12 2.5 12z" opacity=".45"/><path d="M4 20L20 4"/></svg>',
  image: '<svg viewBox="0 0 24 24"><rect x="3.5" y="5" width="17" height="14" rx="2"/><path d="M3.5 16l5-5 4 4 3-3 5 5"/></svg>',
  video: '<svg viewBox="0 0 24 24"><rect x="3.5" y="6" width="12" height="12" rx="2"/><path d="M15.5 10.5l5-3v9l-5-3z"/></svg>',
};

// The reference list, top layer first as it lies on the sheet, and the settings of the selected one.
function refreshRefs() {
  if (!doc) return;
  const list = $('#refList');
  list.replaceChildren(...[...refs].reverse().map(r => {
    const row = document.createElement('div');
    row.className = `layer${r === sel ? ' sel' : ''}${r.visible ? '' : ' off'}`;
    row.title = r.file;
    row.innerHTML = `<button class="eye" title="Показати / сховати">${r.visible ? ICONS.eye : ICONS.hidden}</button><i class="kind">${ICONS[r.kind]}</i><b></b>
      <button class="mv" data-d="1" title="Вище"${r === refs[refs.length - 1] ? ' disabled' : ''}>↑</button><button class="mv" data-d="-1" title="Нижче"${r === refs[0] ? ' disabled' : ''}>↓</button><button class="x" title="Прибрати цей референс">×</button>`;
    row.querySelector('b').textContent = r.name;
    row.onclick = e => {
      const b = e.target.closest('button');
      if (!b) return selectRef(r);
      if (b.classList.contains('eye')) setRefVisible(r, !r.visible);
      else if (b.classList.contains('mv')) moveRef(r, +b.dataset.d);
      else if (b.classList.contains('x')) removeReference(r);
    };
    return row;
  }));
  $('#refEmpty').hidden = refs.length > 0;
  $('#refInfo').hidden = !sel;
  $('#refBtn').classList.toggle('on', refs.some(r => r.visible));
  $('#refBtn').disabled = !refs.length;
  $('#xfBtn').disabled = !refs.length;
  $('#xfBtn').classList.toggle('on', xform);
  $('#refXform').classList.toggle('on', xform);
  $('#refXform').firstChild.textContent = xform ? 'Готово ' : 'Трансформувати ';
  if (!sel) return;
  $('#refOpacity').value = Math.round(sel.opacity * 100);
  $('#refOpacityOut').textContent = `${Math.round(sel.opacity * 100)}%`;
  $('#refVideo').hidden = sel.kind !== 'video';
  if (sel.kind === 'video') {
    $('#refMeta').textContent = `Відео ${sel.width}×${sel.height} · ${fmtFps(sel.fps)} к/с · ${sel.duration.toFixed(2)} с${sel.hasAudio ? ' · зі звуком' : ''}`;
    $('#refSound').checked = sel.sound;
    $('#refSound').disabled = !sel.hasAudio;
    $('#refOffset').value = sel.offset;
    $('#refOffset').max = sel.frameCount - 1;
  } else {
    $('#refMeta').textContent = `Картинка ${sel.width}×${sel.height}`;
  }
}

function buildPalette() {
  $('#colors').replaceChildren(...PALETTE.map((c, i) => {
    const b = document.createElement('button');
    b.dataset.color = c;
    b.title = `Колір ${i + 1}`;
    b.innerHTML = `<i style="--c:${c}"></i>`;
    b.onclick = () => setColor(c);
    return b;
  }));
}

function wire() {
  buildPalette();
  const on = (sel, ev, fn) => $(sel).addEventListener(ev, fn);
  $$('#tools button').forEach(b => { b.onclick = () => setTool(b.dataset.tool); });
  $$('#target button').forEach(b => { b.onclick = () => setEditSketch(b.dataset.target === 'sketch'); });
  on('#sizeRange', 'input', e => setSize(rangeToSize(+e.target.value)));
  on('#sizeNum', 'change', e => setSize(+e.target.value || 1));
  on('#colorPick', 'input', e => setColor(e.target.value));
  on('#undoBtn', 'click', undo);
  on('#redoBtn', 'click', redo);
  on('#onionBtn', 'click', () => toggleOnion());
  on('#refBtn', 'click', () => toggleRefs());
  on('#xfBtn', 'click', () => setXform());
  on('#mirrorBtn', 'click', () => toggleMirror());
  on('#zoomBtn', 'click', fit);
  on('#helpBtn', 'click', helpDialog);
  on('#donateBtn', 'click', () => af.openDonate());
  on('#exportBtn', 'click', () => guarded(exportDialog));
  on('#newBtn', 'click', () => guarded(newProject));
  on('#openBtn', 'click', () => guarded(() => openProject()));
  on('#saveBtn', 'click', () => guarded(() => save()));

  on('#pressure', 'change', e => { prefs.pressure = e.target.checked; savePrefs(); });
  on('#smoothing', 'input', e => {
    prefs.smoothing = +e.target.value / 100;
    $('#smoothingOut').textContent = `${e.target.value}%`;
    savePrefs();
  });
  on('#angle', 'input', e => {
    prefs.angle = +e.target.value;
    $('#angleOut').textContent = `${prefs.angle}°`;
    shapeCursor();
    savePrefs();
  });

  on('#onionOn', 'change', e => toggleOnion(e.target.checked));
  $$('.stepper').forEach(s => {
    const [minus, plus] = s.querySelectorAll('button');
    const step = d => {
      prefs.onion[s.dataset.key] = clamp(prefs.onion[s.dataset.key] + d, 0, 5);
      savePrefs();
      refreshUI();
      requestRender();
    };
    minus.onclick = () => step(-1);
    plus.onclick = () => step(1);
  });
  for (const k of ['prevColor', 'nextColor']) {
    on(`#${k}`, 'input', e => {
      prefs.onion[k] = e.target.value;
      e.target.nextElementSibling.style.setProperty('--c', e.target.value);
      savePrefs();
      requestRender();
    });
  }
  on('#onionOpacity', 'input', e => {
    prefs.onion.opacity = +e.target.value / 100;
    $('#onionOpacityOut').textContent = `${e.target.value}%`;
    savePrefs();
    requestRender();
  });

  on('#refLoad', 'click', pickReference);
  on('#refOpacity', 'input', e => {
    sel.opacity = +e.target.value / 100;
    $('#refOpacityOut').textContent = `${e.target.value}%`;
    requestRender();
    changed();
  });
  on('#refXform', 'click', () => setXform());
  on('#refFlip', 'click', () => flipRef());
  on('#refReset', 'click', () => resetRef());
  on('#xfBadge', 'click', e => {
    const a = e.target.closest('[data-xf]')?.dataset.xf;
    if (a === 'flip') flipRef();
    else if (a === 'reset') resetRef();
    else if (a === 'done') setXform(false);
  });
  on('#refSound', 'change', e => setRefSound(sel, e.target.checked));
  on('#refOffset', 'change', e => {
    sel.offset = clamp(Math.round(+e.target.value || 0), 0, sel.frameCount - 1);
    e.target.value = sel.offset;
    layoutVideo(sel);
    syncReference();
    changed();
  });
  on('#refFill', 'click', fillToVideo);
  on('#sketchMode', 'click', () => setEditSketch());
  on('#sketchVisible', 'change', e => toggleSketch(e.target.checked));
  on('#sketchOpacity', 'input', e => {
    doc.sketch.opacity = +e.target.value / 100;
    $('#sketchOpacityOut').textContent = `${e.target.value}%`;
    requestRender();
    changed();
  });
  on('#frameToSketch', 'click', frameToSketch);
  on('#sketchToFrame', 'click', sketchToFrame);
  on('#sketchClear', 'click', () => clearFrame(doc.sketch));
  on('#paperColor', 'input', e => {
    doc.paper = e.target.value;
    requestRender();
    e.target.nextElementSibling.style.setProperty('--c', doc.paper);
    strip.querySelectorAll('.thumb').forEach(t => { t.style.background = doc.paper; });
    changed();
  });

  on('#firstBtn', 'click', () => go(0));
  on('#prevBtn', 'click', () => go(cur - 1));
  on('#playBtn', 'click', togglePlay);
  on('#nextBtn', 'click', () => go(cur + 1));
  on('#lastBtn', 'click', () => go(doc.frames.length - 1));
  on('#loopBtn', 'click', () => {
    prefs.loop = !prefs.loop;
    savePrefs();
    refreshUI();
  });
  on('#fps', 'change', e => {
    doc.fps = clamp(+e.target.value || doc.fps, 1, 120);
    const same = videos().find(v => Math.abs(doc.fps - v.fps) < 0.01);
    if (same) doc.fps = same.fps; // typed 29.97, means the video's own rate
    e.target.value = Math.round(doc.fps * 1000) / 1000;
    relayoutVideo();
    changed();
    refreshUI();
  });
  $$('#stepSeg button').forEach(b => {
    b.onclick = () => {
      prefs.step = +b.dataset.step;
      savePrefs();
      refreshUI();
    };
  });
  on('#addBtn', 'click', addFrame);
  on('#dupBtn', 'click', duplicateFrame);
  on('#delBtn', 'click', deleteFrame);
  on('#holdMinus', 'click', () => changeHold(-1));
  on('#holdPlus', 'click', () => changeHold(1));

  // Sliders, toggles and buttons must not keep focus: arrows, space and letters belong to the animation.
  document.addEventListener('change', e => {
    if (e.target.matches('input[type=range], input[type=checkbox], input[type=color]')) e.target.blur();
  });
  document.addEventListener('pointerup', () => {
    const a = document.activeElement;
    if (a?.matches?.('button, input[type=range], input[type=checkbox]') && !a.closest('#modal')) a.blur();
  });

  // Drag a picture, a video or a project onto the window.
  let dragDepth = 0;
  addEventListener('dragenter', e => {
    e.preventDefault();
    dragDepth++;
    stage.classList.add('drop');
  });
  addEventListener('dragleave', () => {
    if (--dragDepth <= 0) stage.classList.remove('drop');
  });
  addEventListener('dragover', e => e.preventDefault());
  addEventListener('drop', e => {
    e.preventDefault();
    dragDepth = 0;
    stage.classList.remove('drop');
    const file = e.dataTransfer.files[0];
    const p = file && af.pathForFile(file);
    if (!p) return;
    if (/\.artframes$/i.test(p)) guarded(() => openProject(p));
    else guarded(() => loadReference(p));
  });
}

function toggleOnion(v = !prefs.onion.on) {
  prefs.onion.on = v;
  savePrefs();
  refreshUI();
  requestRender();
}

function toggleMirror() {
  view.mirror = !view.mirror;
  applyView();
}

// ---------- keyboard ----------

const typing = t => t?.matches?.('input[type=number], input[type=text], textarea, select');

addEventListener('keydown', e => {
  if (e.code === 'F9') {
    e.preventDefault();
    if (doc) cursorRescue();
    return;
  }
  if ($('#modal').childElementCount) {
    if (e.key === 'Escape') {
      e.preventDefault();
      const cancel = modalResolve?.buttons?.find(b => !b.primary);
      closeModal(cancel ? cancel.value : undefined);
    } else if (e.key === 'Enter' && !typing(e.target)) {
      e.preventDefault();
      const primary = modalResolve?.buttons?.find(b => b.primary);
      if (primary) closeModal(primary.value);
    } else if (e.key === 'Enter' && typing(e.target)) {
      e.target.dispatchEvent(new Event('input', { bubbles: true }));
      const primary = modalResolve?.buttons?.find(b => b.primary);
      if (primary) closeModal(primary.value);
    }
    return;
  }
  if (typing(e.target)) {
    if (e.key === 'Escape' || e.key === 'Enter') e.target.blur();
    return;
  }
  if (!doc || stroke || drag) {
    if (e.code === 'Tab') e.preventDefault(); // mid-stroke: ignored, and the focus stays put
    return;
  }
  const k = e.code;
  const ctrl = e.ctrlKey || e.metaKey;
  let handled = true;
  if (ctrl) {
    if (k === 'KeyZ') e.shiftKey ? redo() : undo();
    else if (k === 'KeyY') redo();
    else if (k === 'KeyS') guarded(() => save(e.shiftKey));
    else if (k === 'KeyO') guarded(() => openProject());
    else if (k === 'KeyN') guarded(newProject);
    else if (k === 'KeyE') guarded(exportDialog);
    else if (k === 'KeyI') pickReference();
    else if (k === 'KeyT') setXform();
    else if (k === 'Digit0' || k === 'Numpad0') fit();
    else if (k === 'Digit1') zoomAt(1 / view.zoom, stage.clientWidth / 2, stage.clientHeight / 2);
    else if (k === 'Equal' || k === 'NumpadAdd') zoomAt(1.25, stage.clientWidth / 2, stage.clientHeight / 2);
    else if (k === 'Minus' || k === 'NumpadSubtract') zoomAt(0.8, stage.clientWidth / 2, stage.clientHeight / 2);
    else if (k === 'Delete' || k === 'Backspace') deleteFrame();
    else handled = false;
  } else if (k === 'Space') {
    if (!e.repeat) {
      space.down = true;
      space.used = false;
      flag('space', true, 'Space down');
    }
  } else if (e.altKey && (k === 'ArrowLeft' || k === 'ArrowRight')) {
    moveFrame(cur, cur + (k === 'ArrowLeft' ? -1 : 1));
  } else if (k === 'ArrowLeft' || k === 'Comma') go(cur - 1);
  else if (k === 'ArrowRight' || k === 'Period') go(cur + 1);
  else if (k === 'Home') go(0);
  else if (k === 'End') go(doc.frames.length - 1);
  else if (k === 'KeyB') setTool('round');
  else if (k === 'KeyF') setTool('flat');
  else if (k === 'KeyE') setTool('eraser');
  else if (k === 'BracketLeft') setSize(Math.min(prefs.sizes[prefs.tool] - 1, prefs.sizes[prefs.tool] / 1.2));
  else if (k === 'BracketRight') setSize(Math.max(prefs.sizes[prefs.tool] + 1, prefs.sizes[prefs.tool] * 1.2));
  else if (/^Digit[1-6]$/.test(k)) setColor(PALETTE[+k.slice(5) - 1]);
  else if (k === 'KeyN') addFrame();
  else if (k === 'KeyD') duplicateFrame();
  else if ((k === 'Delete' || k === 'Backspace') && xform) handled = true; // the frame is not what is being edited
  else if (k === 'Delete' || k === 'Backspace') e.shiftKey ? deleteFrame() : clearFrame();
  else if (k === 'Minus' || k === 'NumpadSubtract') changeHold(-1);
  else if (k === 'Equal' || k === 'NumpadAdd') changeHold(1);
  else if (k === 'KeyO') toggleOnion();
  else if (k === 'Tab') setEditSketch();
  else if (k === 'KeyT') setXform();
  else if (k === 'KeyH' && xform) flipRef();
  else if ((k === 'Escape' || k === 'Enter' || k === 'NumpadEnter') && xform) setXform(false);
  else if (k === 'Escape' && editSketch) setEditSketch(false);
  else if (k === 'KeyR') e.shiftKey ? toggleSketch() : toggleRefs();
  else if (k === 'KeyM') toggleMirror();
  else if (k === 'Digit0' || k === 'Numpad0') fit();
  else if (k === 'Enter' || k === 'NumpadEnter') togglePlay();
  else if (k === 'F1' || (k === 'Slash' && e.shiftKey)) helpDialog();
  else handled = false;
  if (handled) e.preventDefault();
});

addEventListener('keyup', e => {
  if (e.code !== 'Space' || !space.down) return;
  space.down = false;
  flag('space', false, 'Space up');
  if (!space.used && !typing(e.target) && !$('#modal').childElementCount) togglePlay();
  e.preventDefault();
});

addEventListener('blur', e => {
  if (e.target !== window) return; // focus moving between buttons is not the window losing it
  space.down = false;
  flag('space', false, 'window blur');
});

// ---------- start ----------

async function start() {
  wire();
  setDoc({ ...prefs.newDoc });
  $('#donateBtn').hidden = !(await af.donateAvailable());
  const pending = await af.pendingFile();
  if (pending) return guarded(() => openProject(pending));
  const saved = await af.autosaveInfo();
  if (!saved) return;
  const when = new Date(saved.mtime).toLocaleString('uk');
  const answer = await modal({
    title: 'Відновити роботу?',
    body: html(`<p>Знайдено автозбереження від ${esc(when)}: схоже, минулого разу програму закрили, не зберігши проєкт.</p>`),
    buttons: [{ label: 'Ні, почати з чистого', value: false }, { label: 'Відновити', value: true, primary: true }],
  });
  if (answer) {
    await guarded(async () => {
      await applyProject(await af.autosaveLoad(), null);
      setDirty(true);
    });
  } else {
    await af.autosaveClear();
  }
}

start();

// Handle for the self-test (selftest.js drives real input and reads state through it).
window.__af = {
  get doc() { return doc; },
  get cur() { return cur; },
  get ref() { return sel; },
  get refs() { return refs; },
  get xform() { return xform; },
  setXform,
  selectRef: i => selectRef(refs[i]),
  get prefs() { return prefs; },
  get playing() { return !!playing; },
  get undoDepth() { return undoStack.length; },
  get editSketch() { return editSketch; },
  get sketch() { return { visible: doc.sketch.visible, opacity: doc.sketch.opacity, drawn: !!doc.sketch.layer }; },
  get view() { return view; },
  perf,
  setDoc,
  go,
  loadReference: async (file, o) => void (await loadReference(file, o)),
  exportTo,
  save: async file => af.saveProject(file, await serialize()),
  open: async file => applyProject(await af.loadProject(file), file),
  gpu,
  // Premultiplied RGBA of one drawing, or of a part of the scene at 1:1: 'onion', 'ref', 'sketch' (the own
  // reference as drawn) or 'scene' (what the sheet shows, without ghosts).
  readFrame: i => {
    const f = doc.frames[i];
    return f?.layer ? gpu.read(f.layer) : null;
  },
  readLayer: (name, x = 0, y = 0, w = doc.width, h = doc.height) => {
    const only = {
      onion: { paper: false, reference: false, sketch: false, drawing: false },
      ref: { paper: false, sketch: false, ghosts: false, drawing: false, refOpacity: 1 },
      scene: { ghosts: false },
    }[name];
    const ops = name === 'sketch' ? (doc.sketch.layer ? [{ layer: doc.sketch.layer }] : []) : sceneOps(only);
    return renderDoc('probe', w, h, ops, { x, y });
  },
  setTool,
  setSize,
  setColor,
  fit,
  flushThumbs,
};
