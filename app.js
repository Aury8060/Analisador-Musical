'use strict';
/* ============================================================
   Analisador Musical — análise local via Web Audio API
   BPM / tonalidade / escala / acordes / melodia estimada
   ============================================================ */
(function(){

/* ---------- Constantes ---------- */
var NOTES  = ['C','C#','D','D#','E','F','F#','G','G#','A','A#','B'];
var SOLFEGE= ['Dó','Dó#','Ré','Ré#','Mi','Fá','Fá#','Sol','Sol#','Lá','Lá#','Si'];
// Perfis de Krumhansl-Schmuckler (iniciam em Dó/C)
var MAJOR_PROFILE = [6.35,2.23,3.48,2.33,4.38,4.09,2.52,5.19,2.39,3.66,2.29,2.88];
var MINOR_PROFILE = [6.33,2.68,3.52,5.38,2.60,3.53,2.54,4.75,3.98,2.69,3.34,3.17];
// Templates de acorde (raiz no índice 0, com pesos)
var CHORD_TEMPLATES = [
  {suffix:'',     pat:[1,0,0,0,0.85,0,0,0.70,0,0,0,0]},     // maior
  {suffix:'m',    pat:[1,0,0,0.85,0,0,0,0.70,0,0,0,0]},    // menor
  {suffix:'dim',  pat:[1,0,0,0.85,0,0,0.70,0,0,0,0,0]},   // diminuto
  {suffix:'7',    pat:[1,0,0,0,0.85,0,0,0.70,0,0,0.55,0]}, // dominante 7
  {suffix:'m7',   pat:[1,0,0,0.85,0,0,0,0.70,0,0,0.55,0]},// menor 7
  {suffix:'maj7', pat:[1,0,0,0,0.85,0,0,0.70,0,0,0,0.55]} // maior 7
];
var TARGET_SR = 22050;

/* ---------- Estado ---------- */
var audioCtx = null, masterGain = null;
var audioBuffer = null, mono = null, sr = TARGET_SR;
var analysis = null; // {bpm,keyRoot,keyMode,scaleNotes,chords,notes,duration,waveform}
var pb = {playing:false, source:null, startedAt:0, offset:0, raf:0, lastChordIdx:-1};

/* ---------- DOM ---------- */
var $ = function(id){ return document.getElementById(id); };
var dropZone=$('dropZone'), fileBtn=$('fileBtn'), fileInput=$('fileInput'),
    urlInput=$('urlInput'), urlBtn=$('urlBtn'),
    playerSection=$('playerSection'), trackName=$('trackName'),
    waveCanvas=$('waveform'), playBtn=$('playBtn'), stopBtn=$('stopBtn'),
    volume=$('volume'), curTime=$('curTime'), totTime=$('totTime'),
    progressBox=$('progressBox'), progressText=$('progressText'), progressBar=$('progressBar'),
    results=$('results'), exportBtn=$('exportBtn'), toast=$('toast');

/* ---------- Utilidades ---------- */
function fmtTime(s){
  if(!isFinite(s)||s<0) s=0;
  var m=Math.floor(s/60), ss=Math.floor(s%60);
  return m+':'+(ss<10?'0':'')+ss;
}
function midiToName(m){ return NOTES[((m%12)+12)%12] + (Math.floor(m/12)-1); }
function pearson(a,b){
  var i,ma=0,mb=0,n=a.length;
  for(i=0;i<n;i++){ma+=a[i];mb+=b[i];} ma/=n; mb/=n;
  var num=0,da=0,db=0;
  for(i=0;i<n;i++){var x=a[i]-ma,y=b[i]-mb;num+=x*y;da+=x*x;db+=y*y;}
  if(da===0||db===0) return 0;
  return num/Math.sqrt(da*db);
}
function cosine(a,b){
  var i,dot=0,na=0,nb=0,n=a.length;
  for(i=0;i<n;i++){dot+=a[i]*b[i];na+=a[i]*a[i];nb+=b[i]*b[i];}
  if(na===0||nb===0) return 0;
  return dot/Math.sqrt(na*nb);
}
function hann(N){ var w=new Float32Array(N); for(var i=0;i<N;i++) w[i]=0.5*(1-Math.cos(2*Math.PI*i/(N-1))); return w; }
function nextPow2(v){ var p=1; while(p<v) p<<=1; return p; }

/* ---------- FFT (Cooley-Tukey radix-2, in-place) ---------- */
function fft(re, im){
  var n = re.length, i, j, k, len, half, ang, wr, wi, cwr, cwi, ur, ui, vr, vi, bit;
  for(i=1,j=0;i<n;i++){ bit=n>>1; for(;j&bit;bit>>=1) j^=bit; j^=bit;
    if(i<j){ var tr=re[i]; re[i]=re[j]; re[j]=tr; var ti=im[i]; im[i]=im[j]; im[j]=ti; } }
  for(len=2;len<=n;len<<=1){
    half=len>>1; ang=-2*Math.PI/len; wr=Math.cos(ang); wi=Math.sin(ang);
    for(i=0;i<n;i+=len){
      cwr=1; cwi=0;
      for(k=0;k<half;k++){
        ur=re[i+k]; ui=im[i+k];
        vr=re[i+k+half]*cwr - im[i+k+half]*cwi;
        vi=re[i+k+half]*cwi + im[i+k+half]*cwr;
        re[i+k]=ur+vr; im[i+k]=ui+vi;
        re[i+k+half]=ur-vr; im[i+k+half]=ui-vi;
        var nwr=cwr*wr - cwi*wi; cwi=cwr*wi + cwi*wr; cwr=nwr;
      }
    }
  }
}

/* ---------- Reamostragem para mono 22050 Hz ---------- */
function toMono(buffer){
  return new Promise(function(resolve){
    var len = Math.ceil(buffer.duration * TARGET_SR);
    var off = new (window.OfflineAudioContext||window.webkitOfflineAudioContext)(1, len, TARGET_SR);
    var src = off.createBufferSource(); src.buffer = buffer;
    src.connect(off.destination); src.start(0);
    off.startRendering().then(function(rb){
      resolve({data: rb.getChannelData(0).slice(), sr: TARGET_SR});
    });
  });
}

/* ---------- Cromagrama ---------- */
function computeChromagram(x, sr){
  var N=2048, hop=1024, win=hann(N), frames=[];
  var re=new Float32Array(N), im=new Float32Array(N);
  var ref=440;
  for(var start=0; start+N<=x.length; start+=hop){
    for(var i=0;i<N;i++){ re[i]=x[start+i]*win[i]; im[i]=0; }
    fft(re,im);
    var chroma=new Float32Array(12), sum=0;
    for(var k=2;k<N/2;k++){
      var f=k*sr/N;
      if(f<60||f>4200) continue;
      var mag=re[k]*re[k]+im[k]*im[k];
      var pc=((Math.round(12*Math.log2(f/ref)+69))%12+12)%12;
      chroma[pc]+=mag; sum+=mag;
    }
    if(sum>0) for(i=0;i<12;i++) chroma[i]/=sum;
    frames.push(chroma);
  }
  return {frames: frames, hopSec: hop/sr};
}

/* ---------- Detecção de tonalidade ---------- */
function findKey(globalChroma){
  var best={score:-Infinity, root:0, mode:'major'};
  for(var root=0; root<12; root++){
    var rot=new Array(12);
    for(var i=0;i<12;i++) rot[i]=globalChroma[(root+i)%12];
    var sMaj=pearson(rot, MAJOR_PROFILE);
    var sMin=pearson(rot, MINOR_PROFILE);
    if(sMaj>best.score) best={score:sMaj, root:root, mode:'major'};
    if(sMin>best.score) best={score:sMin, root:root, mode:'minor'};
  }
  return best;
}
function scaleNotes(root, mode){
  var intervs = mode==='major' ? [0,2,4,5,7,9,11] : [0,2,3,5,7,8,10];
  return intervs.map(function(s){ return (root+s)%12; });
}

/* ---------- Detecção de acordes ---------- */
function findChords(chroma){
  var frames=chroma.frames, hopSec=chroma.hopSec;
  var labels=[]; // rótulo por frame: string ou '—'
  var i, root, t, bestScore, bestLabel, rot;
  for(i=0;i<frames.length;i++){
    bestScore=0.45; bestLabel='—'; // limiar de confiança
    for(root=0;root<12;root++){
      rot=new Float32Array(12);
      for(var c=0;c<12;c++) rot[c]=frames[i][(root+c)%12];
      for(t=0;t<CHORD_TEMPLATES.length;t++){
        var sc=cosine(rot, CHORD_TEMPLATES[t].pat);
        if(sc>bestScore){ bestScore=sc; bestLabel=NOTES[root]+CHORD_TEMPLATES[t].suffix; }
      }
    }
    labels.push(bestLabel);
  }
  // Filtro de mediana (janela 5)
  var smoothed=[];
  for(i=0;i<labels.length;i++){
    var counts={};
    for(var d=-2;d<=2;d++){ var idx=i+d; if(idx<0) idx=0; if(idx>=labels.length) idx=labels.length-1;
      counts[labels[idx]]=(counts[labels[idx]]||0)+1; }
    var top='—', topN=0;
    for(var k in counts){ if(counts[k]>topN){topN=counts[k]; top=k;} }
    smoothed.push(top);
  }
  // Junta segmentos consecutivos
  var chords=[], cur=null;
  for(i=0;i<smoothed.length;i++){
    var t0=i*hopSec;
    if(cur && cur.label===smoothed[i]){ cur.dur+=hopSec; }
    else { if(cur) chords.push(cur); cur={label:smoothed[i], time:t0, dur:hopSec}; }
  }
  if(cur) chords.push(cur);
  // Remove segmentos muito curtos (<0.5s) fundindo com o vizinho mais longo
  var changed=true;
  while(changed){
    changed=false;
    for(i=0;i<chords.length;i++){
      if(chords[i].dur<0.5 && chords.length>1){
        var prev=i>0?chords[i-1]:null, next=i<chords.length-1?chords[i+1]:null;
        var target = prev && (!next || prev.dur>=next.dur) ? prev : next;
        target.dur += chords[i].dur;
        if(target===next) next.time = chords[i].time;
        chords.splice(i,1);
        changed=true; break;
      }
    }
  }
  return chords;
}

/* ---------- Detecção de BPM (spectral flux + autocorrelação) ---------- */
function findBPM(x, sr){
  var N=1024, hop=512, win=hann(N);
  var re=new Float32Array(N), im=new Float32Array(N), prevMag=null;
  var flux=[];
  for(var start=0; start+N<=x.length; start+=hop){
    for(var i=0;i<N;i++){ re[i]=x[start+i]*win[i]; im[i]=0; }
    fft(re,im);
    var fl=0;
    for(var k=1;k<N/2;k++){
      var mag=Math.sqrt(re[k]*re[k]+im[k]*im[k]);
      if(prevMag) fl += Math.max(0, mag - prevMag[k]);
    }
    prevMag=new Float32Array(N/2);
    for(k=1;k<N/2;k++) prevMag[k]=Math.sqrt(re[k]*re[k]+im[k]*im[k]);
    flux.push(fl);
  }
  // Suaviza (média móvel 3)
  var sf=new Float32Array(flux.length);
  for(i=1;i<flux.length-1;i++) sf[i]=(flux[i-1]+flux[i]+flux[i+1])/3;
  sf[0]=flux[0]; sf[flux.length-1]=flux[flux.length-1];
  var mean=0; for(i=0;i<sf.length;i++) mean+=sf[i]; mean/=sf.length;
  for(i=0;i<sf.length;i++) sf[i]-=mean;
  // Autocorrelação em lags inteiros
  var L=sf.length, maxLag=Math.min(160, L-1);
  var ac=new Float32Array(maxLag+1);
  for(var lag=8; lag<=maxLag; lag++){
    var c=0;
    for(i=0;i+lag<L;i++) c+=sf[i]*sf[i+lag];
    ac[lag]=c/(L-lag);
  }
  // Avalia BPMs de 50 a 210 (interpola o lag)
  var hopSec=hop/sr, bestBpm=120, bestVal=-Infinity;
  for(var bpm=50; bpm<=210; bpm+=0.5){
    var l = 60/bpm/hopSec;
    if(l<8||l>maxLag) continue;
    var li=Math.floor(l), frac=l-li;
    var v = ac[li]*(1-frac) + (li+1<=maxLag ? ac[li+1]*frac : ac[li]*frac);
    if(v>bestVal){ bestVal=v; bestBpm=bpm; }
  }
  return Math.round(bestBpm);
}

/* ---------- Extração de melodia (pitch por autocorrelação via FFT) ---------- */
function extractMelody(x, sr){
  // Passa-alta suave para atenuar graves: y[n]=x[n]-0.95*x[n-1]
  var hp=new Float32Array(x.length);
  for(var i=1;i<x.length;i++) hp[i]=x[i]-0.95*x[i-1];
  var N=2048, hop=1024, win=hann(N), fftN=4096;
  var re=new Float32Array(fftN), im=new Float32Array(fftN);
  var minLag=Math.round(sr/1400), maxLag=Math.round(sr/90); // ~90–1400 Hz (registro de melodia)
  var seq=[]; // {midi} ou null por frame
  for(var start=0; start+N<=hp.length; start+=hop){
    for(i=0;i<fftN;i++){ re[i]=0; im[i]=0; }
    for(i=0;i<N;i++) re[i]=hp[start+i]*win[i];
    fft(re,im);
    // Espectro de potência
    for(i=0;i<fftN;i++){ re[i]=re[i]*re[i]+im[i]*im[i]; im[i]=0; }
    fft(re,im); // IFFT: parte real = autocorrelação / fftN
    var r0=re[0]/fftN;
    if(r0<=0){ seq.push(null); continue; }
    var bestK=-1, bestR=-1;
    for(var k=minLag;k<=maxLag && k<fftN;k++){
      var rk=re[k]/fftN;
      if(rk>bestR){ bestR=rk; bestK=k; }
    }
    var conf = bestR/r0;
    if(conf>0.2 && bestK>0){
      var y0=re[bestK-1]/fftN, y1=bestR, y2=re[bestK+1]/fftN;
      var denom=(y0-2*y1+y2), kk=bestK;
      if(Math.abs(denom)>1e-12) kk = bestK + 0.5*(y0-y2)/denom;
      var f=sr/kk;
      if(f>=80 && f<=1500){
        var midi=Math.round(69+12*Math.log2(f/440));
        seq.push({midi:midi});
      } else seq.push(null);
    } else seq.push(null);
  }
  // Segmenta em notas (funde frames consecutivos da mesma nota)
  var hopSec=hop/sr, notes=[], cur=null;
  for(i=0;i<seq.length;i++){
    var t=i*hopSec, p=seq[i];
    if(p && cur && cur.midi===p.midi){ cur.dur+=hopSec; }
    else {
      if(cur && cur.dur>=0.12) notes.push(cur);
      cur = p ? {midi:p.midi, name:midiToName(p.midi), start:t, dur:hopSec} : null;
    }
  }
  if(cur && cur.dur>=0.12) notes.push(cur);
  return notes;
}

/* ---------- Forma de onda (downsample) ---------- */
function computeWaveform(x, points){
  var out=[], block=Math.floor(x.length/points);
  if(block<1) block=1;
  for(var i=0;i<points;i++){
    var min=1, max=-1, start=i*block;
    for(var j=0;j<block && start+j<x.length;j++){
      var v=x[start+j]; if(v<min)min=v; if(v>max)max=v;
    }
    out.push([min,max]);
  }
  return out;
}

/* ---------- Renderização ---------- */
function drawWaveform(){
  if(!analysis || !waveCanvas) return;
  var dpr=window.devicePixelRatio||1;
  var w=waveCanvas.clientWidth||800, h=110;
  waveCanvas.width=w*dpr; waveCanvas.height=h*dpr;
  var ctx=waveCanvas.getContext('2d'); ctx.scale(dpr,dpr);
  ctx.clearRect(0,0,w,h);
  var wf=analysis.waveform, n=wf.length;
  // grade
  ctx.strokeStyle='rgba(161,161,168,.12)'; ctx.lineWidth=1;
  ctx.beginPath(); ctx.moveTo(0,h/2); ctx.lineTo(w,h/2); ctx.stroke();
  // picos
  ctx.fillStyle='#7aac2b';
  var bw=w/n;
  for(var i=0;i<n;i++){
    var y1=(1-(wf[i][1]+1)/2)*h, y2=(1-(wf[i][0]+1)/2)*h;
    ctx.fillRect(i*bw, Math.min(y1,y2), Math.max(bw,0.6), Math.abs(y2-y1)||1);
  }
  drawWavePlayhead(ctx,w,h);
}
function drawWavePlayhead(ctx,w,h){
  var t=getCurrentTime(), ratio=analysis.duration>0 ? t/analysis.duration : 0;
  ctx.fillStyle='rgba(244,244,245,.85)';
  ctx.fillRect(ratio*w-1, 0, 2, h);
}

function drawPianoRoll(){
  if(!analysis || !analysis.notes.length) return;
  var cv=$('pianoRoll');
  var dpr=window.devicePixelRatio||1;
  var w=cv.clientWidth||800, h=220;
  cv.width=w*dpr; cv.height=h*dpr;
  var ctx=cv.getContext('2d'); ctx.scale(dpr,dpr);
  ctx.clearRect(0,0,w,h);
  var notes=analysis.notes;
  var minMidi=Infinity, maxMidi=-Infinity;
  for(var i=0;i<notes.length;i++){ if(notes[i].midi<minMidi)minMidi=notes[i].midi; if(notes[i].midi>maxMidi)maxMidi=notes[i].midi; }
  minMidi-=2; maxMidi+=2;
  var range=Math.max(maxMidi-minMidi,12);
  var dur=analysis.duration;
  // linhas de oitava
  ctx.strokeStyle='rgba(161,161,168,.1)'; ctx.lineWidth=1;
  for(var m=Math.ceil(minMidi/12)*12; m<=maxMidi; m+=12){
    var y=(1-(m-minMidi)/range)*h;
    ctx.beginPath(); ctx.moveTo(0,y); ctx.lineTo(w,y); ctx.stroke();
  }
  // notas
  for(i=0;i<notes.length;i++){
    var nt=notes[i];
    var x=(nt.start/dur)*w, rw=Math.max((nt.dur/dur)*w, 2);
    var y=(1-(nt.midi-minMidi)/range)*h, rh=Math.max(h/range*0.7, 3);
    var grad=ctx.createLinearGradient(0,y-rh/2,0,y+rh/2);
    grad.addColorStop(0,'#9cc94a'); grad.addColorStop(1,'#7aac2b');
    ctx.fillStyle=grad;
    roundRect(ctx, x, y-rh/2, rw, rh, 2); ctx.fill();
  }
  // playhead
  var t=getCurrentTime(), ratio=dur>0?t/dur:0;
  ctx.strokeStyle='#c4a87c'; ctx.lineWidth=1.5;
  ctx.beginPath(); ctx.moveTo(ratio*w,0); ctx.lineTo(ratio*w,h); ctx.stroke();
}
function roundRect(ctx,x,y,w,h,r){
  ctx.beginPath();
  ctx.moveTo(x+r,y); ctx.arcTo(x+w,y,x+w,y+h,r); ctx.arcTo(x+w,y+h,x,y+h,r);
  ctx.arcTo(x,y+h,x,y,r); ctx.arcTo(x,y,x+w,y,r); ctx.closePath();
}

function renderResults(){
  $('statBpm').textContent = analysis.bpm;
  $('statBpmSub').textContent = 'batidas por minuto';
  var keyName = NOTES[analysis.keyRoot] + ' ' + (analysis.keyMode==='major'?'maior':'menor');
  var keySolfege = SOLFEGE[analysis.keyRoot] + ' ' + (analysis.keyMode==='major'?'maior':'menor');
  $('statKey').textContent = keyName;
  $('statKeySub').textContent = keySolfege + ' — ' + (analysis.keyMode==='major'?'campo maior':'campo menor');
  var sc=$('statScale'); sc.innerHTML='';
  analysis.scaleNotes.forEach(function(n){
    var c=document.createElement('span'); c.className='scale-chip';
    c.textContent=NOTES[n]; sc.appendChild(c);
  });
  $('statScaleSub').textContent = analysis.keyMode==='major' ? 'escala maior (natural)' : 'escala menor (natural)';
  $('statDur').textContent = fmtTime(analysis.duration);
  $('statDurSub').textContent = 'minutos : segundos';

  // Acordes
  var ct=$('chordTimeline'); ct.innerHTML='';
  analysis.chords.forEach(function(ch, idx){
    var el=document.createElement('div'); el.className='chord-chip'; el.dataset.idx=idx;
    el.innerHTML='<div class="chord-name">'+ch.label+'</div>'+
                 '<div class="chord-time">'+fmtTime(ch.time)+'</div>'+
                 '<div class="chord-dur">'+ch.dur.toFixed(1)+'s</div>';
    el.addEventListener('click', function(){ seek(ch.time); play(); });
    ct.appendChild(el);
  });
  $('chordCount').textContent = analysis.chords.length + ' acorde(s) detectado(s)';

  // Notas
  var nl=$('noteList'); nl.innerHTML='';
  analysis.notes.slice(0,300).forEach(function(nt){
    var p=document.createElement('span'); p.className='note-pill';
    p.innerHTML=nt.name+'<span class="nt">'+fmtTime(nt.start)+'</span>';
    p.addEventListener('click', function(){ seek(nt.start); play(); });
    nl.appendChild(p);
  });
  $('noteCount').textContent = analysis.notes.length + ' nota(s) — primeira melodia estimada';

  results.classList.remove('hidden');
  exportBtn.classList.remove('hidden');
  if(window.lucide) lucide.createIcons();
  drawWaveform(); drawPianoRoll();
  results.scrollIntoView({behavior:'smooth', block:'start'});
}

/* ---------- Playback ---------- */
function ensureCtx(){
  if(!audioCtx){
    var AC=window.AudioContext||window.webkitAudioContext;
    audioCtx=new AC();
    masterGain=audioCtx.createGain();
    masterGain.gain.value=parseFloat(volume.value);
    masterGain.connect(audioCtx.destination);
  }
  if(audioCtx.state==='suspended') audioCtx.resume();
}
function getCurrentTime(){
  if(!pb.playing) return pb.offset;
  return pb.offset + (audioCtx.currentTime - pb.startedAt);
}
function stopSource(){
  if(pb.source){ try{ pb.source.onended=null; pb.source.stop(); }catch(e){} pb.source.disconnect(); pb.source=null; }
}
function play(){
  if(!audioBuffer) return;
  ensureCtx();
  if(pb.offset>=audioBuffer.duration-0.05) pb.offset=0;
  stopSource();
  var src=audioCtx.createBufferSource();
  src.buffer=audioBuffer;
  src.connect(masterGain);
  src.start(0, pb.offset);
  src.onended=function(){
    if(pb.playing && getCurrentTime()>=audioBuffer.duration-0.1){
      pb.playing=false; pb.offset=0; updatePlayIcon();
    }
  };
  pb.source=src;
  pb.startedAt=audioCtx.currentTime;
  pb.playing=true;
  updatePlayIcon();
  cancelAnimationFrame(pb.raf); tick();
}
function pause(){
  if(!pb.playing) return;
  pb.offset=getCurrentTime();
  stopSource();
  pb.playing=false;
  cancelAnimationFrame(pb.raf);
  updatePlayIcon();
  drawWaveform(); drawPianoRoll();
}
function seek(t){
  pb.offset=Math.max(0, Math.min(t, audioBuffer? audioBuffer.duration:0));
  if(!pb.playing){ drawWaveform(); drawPianoRoll(); curTime.textContent=fmtTime(pb.offset); }
}
function updatePlayIcon(){
  playBtn.innerHTML = pb.playing ? '<i data-lucide="pause"></i>' : '<i data-lucide="play"></i>';
  if(window.lucide) lucide.createIcons();
}
function tick(){
  if(!pb.playing) return;
  var t=getCurrentTime();
  curTime.textContent=fmtTime(t);
  // acorde ativo
  if(analysis && analysis.chords){
    var idx=-1;
    for(var i=0;i<analysis.chords.length;i++){
      if(t>=analysis.chords[i].time && t<analysis.chords[i].time+analysis.chords[i].dur) idx=i;
    }
    if(idx!==pb.lastChordIdx){
      pb.lastChordIdx=idx;
      var chips=document.querySelectorAll('.chord-chip');
      chips.forEach(function(c,ci){ c.classList.toggle('active', ci===idx); });
      if(idx>=0 && chips[idx]){
        chips[idx].scrollIntoView({behavior:'smooth', inline:'center', block:'nearest'});
      }
    }
  }
  drawWaveform(); drawPianoRoll();
  pb.raf=requestAnimationFrame(tick);
}

/* ---------- Pipeline de análise ---------- */
function setProgress(text, pct){
  progressBox.classList.remove('hidden');
  progressText.textContent=text;
  progressBar.style.width=(pct||0)+'%';
}
function showToast(msg){
  toast.textContent=msg; toast.classList.remove('hidden');
  clearTimeout(showToast._t);
  showToast._t=setTimeout(function(){ toast.classList.add('hidden'); }, 5000);
}
function nextFrame(){ return new Promise(function(r){ setTimeout(r, 30); }); }

async function analyze(){
  try{
    setProgress('Reamostrando áudio…', 5); await nextFrame();
    var res = await toMono(audioBuffer);
    mono=res.data; sr=res.sr;
    analysis={duration: audioBuffer.duration};

    setProgress('Calculando forma de onda…', 12); await nextFrame();
    analysis.waveform = computeWaveform(mono, 1600);
    totTime.textContent=fmtTime(audioBuffer.duration);
    drawWaveform();

    setProgress('Construindo cromagrama (FFT)…', 25); await nextFrame();
    var chroma = computeChromagram(mono, sr);

    setProgress('Identificando tonalidade e escala…', 45); await nextFrame();
    var global=new Float32Array(12);
    for(var i=0;i<chroma.frames.length;i++) for(var c=0;c<12;c++) global[c]+=chroma.frames[i][c];
    for(c=0;c<12;c++) global[c]/=chroma.frames.length;
    var key=findKey(global);
    analysis.keyRoot=key.root; analysis.keyMode=key.mode;
    analysis.scaleNotes=scaleNotes(key.root, key.mode);

    setProgress('Detectando progressão de acordes…', 60); await nextFrame();
    analysis.chords=findChords(chroma);

    setProgress('Medindo BPM (spectral flux)…', 75); await nextFrame();
    analysis.bpm=findBPM(mono, sr);

    setProgress('Extraindo melodia (pitch detection)…', 88); await nextFrame();
    analysis.notes=extractMelody(mono, sr);

    setProgress('Finalizando…', 100); await nextFrame();
    progressBox.classList.add('hidden');
    renderResults();
  }catch(err){
    console.error(err);
    progressBox.classList.add('hidden');
    showToast('Erro na análise: '+err.message);
  }
}

/* ---------- Carregamento ---------- */
async function loadArrayBuffer(buf, name){
  ensureCtx();
  try{
    audioBuffer = await audioCtx.decodeAudioData(buf.slice(0));
  }catch(e){
    showToast('Não foi possível decodificar este áudio. Formato não suportado pelo navegador.');
    return;
  }
  trackName.textContent=name;
  playerSection.classList.remove('hidden');
  pb.offset=0; pb.playing=false; pb.lastChordIdx=-1;
  updatePlayIcon();
  playerSection.scrollIntoView({behavior:'smooth', block:'start'});
  analyze();
}

fileBtn.addEventListener('click', function(){ fileInput.click(); });
fileInput.addEventListener('change', function(){
  var f=fileInput.files[0]; if(!f) return;
  var reader=new FileReader();
  reader.onload=function(){ loadArrayBuffer(reader.result, f.name); };
  reader.onerror=function(){ showToast('Erro ao ler o arquivo.'); };
  reader.readAsArrayBuffer(f);
});
urlBtn.addEventListener('click', async function(){
  var url=urlInput.value.trim();
  if(!url){ showToast('Cole um link de áudio (ex: https://…/musica.mp3).'); return; }
  setProgress('Baixando áudio do link…', 5);
  try{
    var resp=await fetch(url, {mode:'cors'});
    if(!resp.ok) throw new Error('HTTP '+resp.status);
    var buf=await resp.arrayBuffer();
    progressBox.classList.add('hidden');
    loadArrayBuffer(buf, url.split('/').pop().split('?')[0] || 'link de áudio');
  }catch(e){
    progressBox.classList.add('hidden');
    showToast('Não foi possível carregar este link (bloqueio CORS provável). YouTube/Spotify não funcionam diretamente — baixe o áudio como arquivo e importe.');
  }
});

/* Drag & drop */
['dragenter','dragover'].forEach(function(ev){
  dropZone.addEventListener(ev, function(e){ e.preventDefault(); dropZone.classList.add('dragover'); });
});
['dragleave','drop'].forEach(function(ev){
  dropZone.addEventListener(ev, function(e){ e.preventDefault(); dropZone.classList.remove('dragover'); });
});
dropZone.addEventListener('drop', function(e){
  var f=e.dataTransfer.files[0]; if(!f) return;
  var reader=new FileReader();
  reader.onload=function(){ loadArrayBuffer(reader.result, f.name); };
  reader.readAsArrayBuffer(f);
});

/* Controles do player */
playBtn.addEventListener('click', function(){ pb.playing ? pause() : play(); });
stopBtn.addEventListener('click', function(){ pause(); seek(0); });
volume.addEventListener('input', function(){ if(masterGain) masterGain.gain.value=parseFloat(volume.value); });
function canvasSeek(canvas, e){
  if(!audioBuffer) return;
  var rect=canvas.getBoundingClientRect();
  var ratio=(e.clientX-rect.left)/rect.width;
  seek(ratio*audioBuffer.duration);
}
waveCanvas.addEventListener('click', function(e){ canvasSeek(waveCanvas, e); });
$('pianoRoll').addEventListener('click', function(e){ canvasSeek($('pianoRoll'), e); });

/* Exportar TXT */
exportBtn.addEventListener('click', function(){
  if(!analysis) return;
  var lines=[];
  lines.push('=== ANÁLISE MUSICAL ===');
  lines.push('Arquivo: '+trackName.textContent);
  lines.push('Duração: '+fmtTime(analysis.duration));
  lines.push('BPM: '+analysis.bpm);
  lines.push('Tonalidade: '+NOTES[analysis.keyRoot]+' '+(analysis.keyMode==='major'?'maior':'menor')+
             ' ('+SOLFEGE[analysis.keyRoot]+' '+(analysis.keyMode==='major'?'maior':'menor')+')');
  lines.push('Escala: '+analysis.scaleNotes.map(function(n){return NOTES[n];}).join(' - '));
  lines.push('');
  lines.push('--- PROGRESSÃO DE ACORDES ---');
  analysis.chords.forEach(function(ch){ lines.push(fmtTime(ch.time)+'  '+ch.label+'  ('+ch.dur.toFixed(1)+'s)'); });
  lines.push('');
  lines.push('--- MELODIA ESTIMADA (notas) ---');
  analysis.notes.forEach(function(nt){ lines.push(fmtTime(nt.start)+'  '+nt.name+'  ('+nt.dur.toFixed(2)+'s)'); });
  var blob=new Blob([lines.join('\n')], {type:'text/plain;charset=utf-8'});
  var a=document.createElement('a');
  a.href=URL.createObjectURL(blob);
  a.download='analise-musical.txt';
  a.click();
  setTimeout(function(){ URL.revokeObjectURL(a.href); }, 1000);
});

/* Redimensiona canvas ao redimensionar janela */
window.addEventListener('resize', function(){
  if(analysis){ drawWaveform(); drawPianoRoll(); }
});

/* Ícones iniciais */
if(window.lucide) lucide.createIcons();

})();
