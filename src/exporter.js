// Export: PNG sequence, GIF, MP4 and WebM, either the animation alone or composited over the reference.
// Every picture is composited on the GPU (src.render) and comes back as RGBA rows that go straight to the GIF
// quantiser or the video encoder. Over a video the video drives the timing: MP4/WebM keep its own frame rate and its
// sound (copied when the container allows it, re-encoded otherwise), PNG and GIF take one picture per animation tick.
import { GIFEncoder, applyPalette, quantize } from '../node_modules/gifenc/dist/gifenc.esm.js';
import {
  BufferTarget, CanvasSink, Conversion, Mp4OutputFormat, Output, QUALITY_HIGH, VideoSample, VideoSampleSource,
  WebMOutputFormat, getFirstEncodableVideoCodec,
} from '../node_modules/mediabunny/dist/bundles/mediabunny.min.mjs';
import { openInput } from './video.js';

const af = window.af;
const tick = () => new Promise(r => setTimeout(r, 0));

async function videoCodec(kind, width, height) {
  const list = kind === 'mp4' ? ['avc', 'hevc', 'vp9', 'av1'] : ['vp9', 'vp8', 'av1'];
  const codec = await getFirstEncodableVideoCodec(list, { width, height });
  if (!codec) throw new Error('У системі немає потрібного відеокодера');
  return codec;
}

const outputFormat = kind => (kind === 'mp4' ? new Mp4OutputFormat({ fastStart: 'in-memory' }) : new WebMOutputFormat());

const rgbaSample = (px, W, H, timestamp, duration) =>
  new VideoSample(px, { format: 'RGBX', codedWidth: W, codedHeight: H, timestamp, duration });

class Cancelled extends Error {}

// src: { width, height, fps, frames, ticks (start tick per frame + total), frameAtTick(t),
//        video (the lowest visible video reference: it drives the timing and gives the sound), videos (all visible
//        video references), render(W, H, { frame, refs, unders, paper, sketch }) -> RGBA, unpremultiply(px) }
//        unders: Map video reference -> its decoded frame for this picture.
// job: { kind: 'png' | 'gif' | 'mp4' | 'webm', target, name, scale, withRef, withSketch, transparent, audio }
export async function runExport(src, job, progress, cancel) {
  const even = job.kind === 'mp4' || job.kind === 'webm';
  const fit = n => {
    const v = Math.max(2, Math.round(n * job.scale));
    return even ? v - (v % 2) : v;
  };
  const W = fit(src.width);
  const H = fit(src.height);
  const refs = !!job.withRef;
  const video = refs && src.video ? src.video : null;
  const others = video ? src.videos.filter(v => v !== video) : [];
  const paper = !(job.transparent && job.kind === 'png');
  const check = () => {
    if (cancel.requested) throw new Cancelled();
  };
  const sketch = !!job.withSketch;
  const picture = (frame, unders) => src.render(W, H, { frame, refs, unders, paper, sketch });

  // Ticks to render: the animation, or the whole video at the animation's frame rate.
  const total = video ? video.ticks() : src.ticks[src.frames.length];
  const frameAt = t => (t < src.ticks[src.frames.length] ? src.frames[src.frameAtTick(t)] : null);

  async function* pictures() {
    if (!video) {
      for (let t = 0; t < total; t++) yield { t, frame: frameAt(t), unders: null };
      return;
    }
    // Every visible video, decoded in step at its own time for each tick. One that ends early holds its last frame.
    const all = [video, ...others];
    const iters = all.map(v => frames(v, W / src.width, total));
    const last = new Map();
    try {
      for (let t = 0; t < total; t++) {
        const got = await Promise.all(iters.map(it => it.next()));
        all.forEach((v, k) => {
          const c = got[k].done ? null : got[k].value?.canvas || null;
          if (c) last.set(v, c);
        });
        yield { t, frame: frameAt(t), unders: new Map(last) };
      }
    } finally {
      for (const it of iters) it.return?.();
    }
  }

  try {
    if (job.kind === 'png') {
      const canvas = Object.assign(document.createElement('canvas'), { width: W, height: H });
      const ctx = canvas.getContext('2d');
      let last = null;
      let bytes = null;
      for await (const { t, frame, unders } of pictures()) {
        check();
        if (unders || frame !== last || !bytes) {
          const px = picture(frame, unders);
          if (!paper) src.unpremultiply(px);
          ctx.putImageData(new ImageData(new Uint8ClampedArray(px.buffer), W, H), 0, 0);
          bytes = new Uint8Array(await (await new Promise(r => canvas.toBlob(r, 'image/png'))).arrayBuffer());
          last = frame;
        }
        await af.writeIn(job.target, `${job.name}_${String(t + 1).padStart(4, '0')}.png`, bytes);
        progress((t + 1) / total);
      }
      return { file: job.target, count: total };
    }

    if (job.kind === 'gif') {
      const gif = GIFEncoder();
      const ms = t => Math.round((t * 1000) / src.fps / 10) * 10; // GIF delays are centiseconds; round the timeline, not each delay
      let count = 0;
      const add = (px, from, to) => {
        const palette = quantize(px, 256);
        gif.writeFrame(applyPalette(px, palette), W, H, { palette, delay: Math.max(20, ms(to) - ms(from)) });
        count++;
      };
      if (video) {
        for await (const { t, frame, unders } of pictures()) {
          check();
          add(picture(frame, unders), t, t + 1);
          progress((t + 1) / total);
          await tick();
        }
      } else {
        // One GIF frame per drawing, held as long as it is exposed.
        for (let i = 0; i < src.frames.length; i++) {
          check();
          add(picture(src.frames[i], null), src.ticks[i], src.ticks[i + 1]);
          progress((i + 1) / src.frames.length);
          await tick();
        }
      }
      gif.finish();
      await af.write(job.target, gif.bytes());
      return { file: job.target, count };
    }

    // MP4 / WebM
    const codec = await videoCodec(job.kind, W, H);
    if (video) return await overVideo(src, job, { W, H, codec, video, others, frameAt, progress, cancel });

    const output = new Output({ format: outputFormat(job.kind), target: new BufferTarget() });
    const source = new VideoSampleSource({ codec, quality: QUALITY_HIGH, keyFrameInterval: 2 });
    output.addVideoTrack(source, { frameRate: src.fps });
    await output.start();
    for (let t = 0; t < total; t++) {
      if (cancel.requested) {
        await output.cancel();
        throw new Cancelled();
      }
      const sample = rgbaSample(picture(frameAt(t), null), W, H, t / src.fps, 1 / src.fps);
      await source.add(sample);
      sample.close();
      progress((t + 1) / total);
    }
    await output.finalize();
    await af.write(job.target, new Uint8Array(output.target.buffer));
    return { file: job.target, count: total, codec };
  } catch (err) {
    if (err instanceof Cancelled) return { cancelled: true };
    throw err;
  }
}

// Frames of a video reference for ticks 0, 1, 2…, decoded at its on-sheet size scaled to the export.
function frames(v, k, total) {
  const sink = new CanvasSink(v.track, {
    width: Math.max(2, Math.round(v.size.w * k)),
    height: Math.max(2, Math.round(v.size.h * k)),
    fit: 'fill',
  });
  const times = Array.from({ length: total }, (_, t) => v.time(t));
  return sink.canvasesAtTimestamps(times)[Symbol.asyncIterator]();
}

// Re-encodes the lowest visible reference video with the drawings (and any other visible references) painted over
// every frame; its audio track rides along.
async function overVideo(src, job, { W, H, codec, video, others, frameAt, progress, cancel }) {
  const input = await openInput(video.file);
  const output = new Output({ format: outputFormat(job.kind), target: new BufferTarget() });
  const k = W / src.width;
  // The decoded frame is drawn with its rotation applied, at the size it takes in the export.
  const sub = Object.assign(document.createElement('canvas'), {
    width: Math.max(2, Math.round(video.size.w * k)),
    height: Math.max(2, Math.round(video.size.h * k)),
  });
  const subCtx = sub.getContext('2d');
  // Other videos follow tick by tick; a few spare ticks cover rounding at the end of the clip.
  const rest = others.map(v => ({ v, it: frames(v, k, video.ticks() + 4), at: -1, canvas: null }));
  const advance = async (o, t) => {
    while (o.at < t) {
      const got = await o.it.next();
      if (got.done) {
        o.at = Infinity;
        break;
      }
      o.at++;
      if (got.value?.canvas) o.canvas = got.value.canvas;
    }
  };
  const start = video.first + video.offset / video.fps;
  let t0 = null;
  const conversion = await Conversion.init({
    input,
    output,
    tracks: 'primary',
    trim: { start },
    showWarnings: false,
    video: {
      codec,
      quality: QUALITY_HIGH,
      allowTransformationMetadata: false,
      processedWidth: W,
      processedHeight: H,
      process: async sample => {
        // The drawing shown on a video frame is the one exposed at the middle of that frame. Sampling the middle
        // keeps 29.97 vs 30000/1001 style rounding from sliding a drawing onto the neighbouring frame.
        if (t0 === null) t0 = sample.timestamp;
        const t = Math.floor((sample.timestamp - t0 + (sample.duration || 1 / video.fps) / 2) * src.fps);
        sample.drawWithFit(subCtx, { fit: 'fill' });
        const unders = new Map([[video, sub]]);
        for (const o of rest) {
          await advance(o, t);
          if (o.canvas) unders.set(o.v, o.canvas);
        }
        const px = src.render(W, H, { frame: frameAt(t), refs: true, unders, sketch: !!job.withSketch });
        return rgbaSample(px, W, H, sample.timestamp, sample.duration);
      },
    },
    audio: job.audio ? {} : { discard: true },
  });
  if (!conversion.isValid) throw new Error('Не вдалося підготувати конвертацію відео');
  const audioLost = job.audio && video.hasAudio && conversion.discardedTracks.some(d => d.track.type === 'audio');
  conversion.onProgress = p => progress(p);
  cancel.abort = () => conversion.cancel();
  try {
    await conversion.execute();
  } catch (err) {
    if (cancel.requested) return { cancelled: true };
    throw err;
  } finally {
    input.dispose?.();
    for (const o of rest) o.it.return?.();
  }
  await af.write(job.target, new Uint8Array(output.target.buffer));
  return { file: job.target, codec, audio: job.audio && video.hasAudio && !audioLost, audioLost };
}
