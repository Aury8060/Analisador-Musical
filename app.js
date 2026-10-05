'use strict';
/* ============================================================
   Analisador Musical PRO — análise local via Web Audio API
   BPM / compasso / tonalidade / escala / acordes (com graus) /
   melodia / solfejo / transposição com áudio / metrônomo / PDF
   ============================================================ */
(function(){

/* ---------- Constantes ---------- */
var NOTES   = ['C','C#','D','D#','E','F','F#','G','G#','A','A#','B'];
var SOLFEGE = ['Dó','Dó#','Ré','Ré#','Mi','Fá','Fá#','Sol','Sol#','Lá','Lá#','Si'];
var MAJOR_PROFILE = [6.35,2.23,3.48,2.33,4.38,4.09,2.52,5.19,2.39,3.66,2.29,2.88];
var MINOR_PROFILE = [6.33,2.68,3.52,5.38,2.60,3.53,2.54,4.75,3.98,2.69,3.34,3.17];
var CHORD_TEMPLATES = [
  {suffix:'',     pat:[1,0,0,0,0.85,0,0,0.70,0,0,0,0]},
  {suffix:'m',    pat:[1,0,0,0.85,0,0,0,0.70,0,0,0,0]},
  {suffix:'dim',  pat:[1,0,0,0.85,0,0,0.70,0,0,0,0,0]},
  {suffix:'7',    pat:[1,0,0,0,0.85,0,0,0.70,0,0,0.55,0]},
  {suffix:'m7',   pat:[1,0,0,0.85,0,0,0,0.70,0,0,0.55,0]},
  {suffix:'maj7', pat:[1,0,0,0,0.85,0,0,0.70,0,0,0,0.55]}
];
var TARGET_SR = 22050;

/* ---------- Estado ---------- */
var audioCtx=null, masterGain=null, metroGain=null;
var audioBuffer=null, mono=null, sr=TARGET_SR;
var analysis=null;
var pb={playing:false, source:null, startedAt:0, offset:0, rate:1, raf:0, lastChordIdx:-1};
var useSolfege=false, transpose=0;
var metro={on:false, timer:null, nextTime:0, beat:0, raf:0, beatsPerBar:4};

/* ---------- DOM ---------- */
var $=function(id){return document.getElementById(id);};
var dropZone=$('dropZone'), fileBtn=$('fileBtn'), fileInput=$('fileInput'),
    urlInput=$('urlInput'), urlBtn=$('urlBtn'),
    playerSection=$('playerSection'), trackName=$('trackName'),
    waveCanvas=$('waveform'), playBtn=$('playBtn'), stopBtn=$('stopBtn'),
    volume=$('volume'), curTime=$('curTime'), totTime=$('totTime'),
    adjustBar=$('adjustBar'),
    solfegeBtn=$('solfegeBtn'),
    metroBtn=$('metroBtn'), metroBpm=$('metroBpm'), beatDots=$('beatDots'),
    transposeSlider=$('transposeSlider'), transposeLabel=$('transposeLabel'), transposeReset=$('transposeReset'),
    progressBox=$('progressBox'), progressText=$('progressText'), progressBar=$('progressBar'),
    results=$('results'), pdfBtn=$('pdfBtn'), wavBtn=$('wavBtn'), toast=$('toast');

/* ---------- Utilidades ---------- */
function fmtTime(s){ if(!isFinite(s)||s<0)s=0; var m=Math.floor(s/60),ss=Math.floor(s%60); return m+':'+(ss<10?'0':'')+ss; }
function mod12(n){ return ((n%12)+12)%12; }
function dispNote(pc){ return (useSolfege?SOLFEGE:NOTES)[mod12(pc)]; }
function dispNoteT(pc){ return dispNote(pc+transpose); }
function midiToName(m){ m=Math.round(m)+transpose; var n=mod12(m), oct=Math.floor(m/12)-1; return dispNote(n)+oct; }
function midiToNameRaw(m){ var n=mod12(m), oct=Math.floor(m/12)-1; return NOTES[n]+oct; }
function pearson(a,b){
  var i,ma=0,mb=0,n=a.length; for(i=0;i<n;i++){ma+=a[i];mb+=b[i];} ma/=n; mb/=n;
  var num=0,da=0,db=0; for(i=0;i<n;i++){var x=a[i]-ma,y=b[i]-mb;num+=x*y;da+=x*x;db+=y*y;}
  if(da===0||db===0)return 0; return num/Math.sqrt(da*db);
}
function cosine(a,b){
  var i,dot=0,na=0,nb=0,n=a.length; for(i=0;i<n;i++){dot+=a[i]*b[i];na+=a[i]*a[i];nb+=b[i]*b[i];}
  if(na===0||nb===0)return 0; return dot/Math.sqrt(na*nb);
}
function hann(N){ var w=new Float32Array(N); for(var i=0;i<N;i++) w[i]=0.5*(1-Math.cos(2*Math.PI*i/(N-1))); return w; }
function transposeRate(){ return Math.pow(2, transpose/12); }

/* ---------- FFT ---------- */
function fft(re,im){
  var n=re.length,i,j,k,len,half,ang,wr,wi,cwr,cwi,ur,ui,vr,vi,bit,tr,ti;
  for(i=1,j=0;i<n;i++){ bit=n>>1; for(;j&bit;bit>>=1) j^=bit; j^=bit;
    if(i<j){ tr=re[i];re[i]=re[j];re[j]=tr; ti=im[i];im[i]=im[j];im[j]=ti; } }
  for(len=2;len<=n;len<<=1){ half=len>>1; ang=-2*Math.PI/len; wr=Math.cos(ang); wi=Math.sin(ang);
    for(i=0;i<n;i+=len){ cwr=1; cwi=0;
      for(k=0;k<half;k++){ ur=re[i+k]; ui=im[i+k];
        vr=re[i+k+half]*cwr - im[i+k+half]*cwi; vi=re[i+k+half]*cwi + im[i+k+half]*cwr;
        re[i+k]=ur+vr; im[i+k]=ui+vi; re[i+k+half]=ur-vr; im[i+k+half]=ui-vi;
        var nwr=cwr*wr-cwi*wi; cwi=cwr*wi+cwi*wr; cwr=nwr;
      } } }
}

/* ---------- Reamostragem mono 22050 ---------- */
function toMono(buffer){
  return new Promise(function(resolve){
    var len=Math.ceil(buffer.duration*TARGET_SR);
    var off=new (window.OfflineAudioContext||window.webkitOfflineAudioContext)(1,len,TARGET_SR);
    var src=off.createBufferSource(); src.buffer=buffer; src.connect(off.destination); src.start(0);
    off.startRendering().then(function(rb){ resolve({data:rb.getChannelData(0).slice(), sr:TARGET_SR}); });
  });
}

/* ---------- Cromagrama ---------- */
function computeChromagram(x,sr){
  var N=2048, hop=1024, win=hann(N), frames=[];
  var re=new Float32Array(N), im=new Float32Array(N);
  for(var start=0; start+N<=x.length; start+=hop){
    for(var i=0;i<N;i++){ re[i]=x[start+i]*win[i]; im[i]=0; }
    fft(re,im);
    var chroma=new Float32Array(12), sum=0;
    for(var k=2;k<N/2;k++){
      var f=k*sr/N; if(f<60||f>4200) continue;
      var mag=re[k]*re[k]+im[k]*im[k];
      var pc=mod12(Math.round(12*Math.log2(f/440)+69));
      chroma[pc]+=mag; sum+=mag;
    }
    if(sum>0) for(i=0;i<12;i++) chroma[i]/=sum;
    frames.push(chroma);
  }
  return {frames:frames, hopSec:hop/sr};
}

/* ---------- Tonalidade ---------- */
function findKey(gc){
  var best={score:-Infinity, root:0, mode:'major'};
  for(var root=0;root<12;root++){
    var rot=new Array(12); for(var i=0;i<12;i++) rot[i]=gc[mod12(root+i)];
    var sM=pearson(rot,MAJOR_PROFILE), sm=pearson(rot,MINOR_PROFILE);
    if(sM>best.score) best={score:sM, root:root, mode:'major'};
    if(sm>best.score) best={score:sm, root:root, mode:'minor'};
  }
  return best;
}
function scaleNotes(root,mode){
  var iv=mode==='major'?[0,2,4,5,7,9,11]:[0,2,3,5,7,8,10];
  return iv.map(function(s){return mod12(root+s);});
}
function chordDegree(ch, keyRoot, mode){
  var diff=mod12(ch.rootIdx-keyRoot);
  var iv=mode==='major'?[0,2,4,5,7,9,11]:[0,2,3,5,7,8,10];
  var idx=iv.indexOf(diff);
  if(idx<0) return 'crom.';
  var num=['I','II','III','IV','V','VI','VII'][idx];
  var suf=ch.suffix;
  var isMin=suf.indexOf('m')>=0 && suf.indexOf('maj')<0;
  var isDim=suf.indexOf('dim')>=0;
  var r=(isMin||isDim)?num.toLowerCase():num;
  if(isDim) r+='°';
  if(suf.indexOf('7')>=0) r+='7';
  return r;
}

/* ---------- Acordes ---------- */
function findChords(chroma){
  var frames=chroma.frames, hopSec=chroma.hopSec, labels=[], i, root, t, c;
  for(i=0;i<frames.length;i++){
    var bestScore=0.45, bestRoot=-1, bestTpl=-1;
    for(root=0;root<12;root++){
      var rot=new Float32Array(12);
      for(c=0;c<12;c++) rot[c]=frames[i][mod12(root+c)];
      for(t=0;t<CHORD_TEMPLATES.length;t++){
        var sc=cosine(rot, CHORD_TEMPLATES[t].pat);
        if(sc>bestScore){ bestScore=sc; bestRoot=root; bestTpl=t; }
      }
    }
    labels.push(bestRoot<0? {root:-1,suffix:''} : {root:bestRoot, suffix:CHORD_TEMPLATES[bestTpl].suffix});
  }
  // mediana janela 5
  var smoothed=[];
  for(i=0;i<labels.length;i++){
    var counts={};
    for(var d=-2;d<=2;d++){ var idx=Math.max(0,Math.min(labels.length-1,i+d));
      var key=labels[idx].root+'|'+labels[idx].suffix; counts[key]=(counts[key]||0)+1; }
    var top='-1|', topN=0;
    for(var k in counts){ if(counts[k]>topN){topN=counts[k];top=k;} }
    var parts=top.split('|'); smoothed.push({root:parseInt(parts[0],10), suffix:parts[1]});
  }
  var chords=[], cur=null;
  for(i=0;i<smoothed.length;i++){
    var t0=i*hopSec, L=smoothed[i];
    var lbl=L.root<0?'—':NOTES[L.root]+L.suffix;
    if(cur && cur.label===lbl){ cur.dur+=hopSec; }
    else { if(cur) chords.push(cur); cur={rootIdx:L.root, suffix:L.suffix, label:lbl, time:t0, dur:hopSec}; }
  }
  if(cur) chords.push(cur);
  // remove segmentos <0.5s
  var changed=true;
  while(changed){ changed=false;
    for(i=0;i<chords.length;i++){
      if(chords[i].dur<0.5 && chords.length>1){
        var prev=i>0?chords[i-1]:null, next=i<chords.length-1?chords[i+1]:null;
        var tgt=prev && (!next||prev.dur>=next.dur)?prev:next;
        tgt.dur+=chords[i].dur; if(tgt===next) next.time=chords[i].time;
        chords.splice(i,1); changed=true; break;
      }
    }
  }
  return chords;
}

/* ---------- BPM + envelope de onsets ---------- */
function findBPM(x,sr){
  var N=1024, hop=512, win=hann(N);
  var re=new Float32Array(N), im=new Float32Array(N), prevMag=null, flux=[];
  for(var start=0; start+N<=x.length; start+=hop){
    for(var i=0;i<N;i++){ re[i]=x[start+i]*win[i]; im[i]=0; }
    fft(re,im);
    var fl=0, mag=new Float32Array(N/2);
    for(var k=1;k<N/2;k++){
      mag[k]=Math.sqrt(re[k]*re[k]+im[k]*im[k]);
      if(prevMag) fl+=Math.max(0, mag[k]-prevMag[k]);
    }
    prevMag=mag; flux.push(fl);
  }
  var sf=new Float32Array(flux.length);
  for(i=1;i<flux.length-1;i++) sf[i]=(flux[i-1]+flux[i]+flux[i+1])/3;
  sf[0]=flux[0]; sf[flux.length-1]=flux[flux.length-1];
  var mean=0; for(i=0;i<sf.length;i++) mean+=sf[i]; mean/=sf.length;
  for(i=0;i<sf.length;i++) sf[i]-=mean;
  var L=sf.length, maxLag=Math.min(160,L-1);
  var ac=new Float32Array(maxLag+1);
  for(var lag=8; lag<=maxLag; lag++){
    var c=0; for(i=0;i+lag<L;i++) c+=sf[i]*sf[i+lag];
    ac[lag]=c/(L-lag);
  }
  var hopSec=hop/sr, bestBpm=120, bestVal=-Infinity;
  for(var bpm=50;bpm<=210;bpm+=0.5){
    var l=60/bpm/hopSec; if(l<8||l>maxLag) continue;
    var li=Math.floor(l), frac=l-li;
    var v=ac[li]*(1-frac)+(li+1<=maxLag?ac[li+1]*frac:ac[li]*frac);
    if(v>bestVal){bestVal=v;bestBpm=bpm;}
  }
  return {bpm:Math.round(bestBpm), onset:sf, hopSec:hopSec};
}

/* ---------- Compasso + fase de beat ---------- */
function estimateMeter(onset, hopSec, bpm){
  var P=60/bpm/hopSec; // período de beat em frames
  var best={beats:4, score:0};
  [2,3,4,6].forEach(function(m){
    var pat=new Float32Array(m), cnt=new Float32Array(m);
    for(var i=0;i<onset.length;i++){
      var ph=(i/P)%m; if(ph<0)ph+=m;
      var b=Math.floor(ph)%m;
      pat[b]+=Math.max(0,onset[i]); cnt[b]++;
    }
    var max=0,min=Infinity,sum=0;
    for(var b2=0;b2<m;b2++){ pat[b2]/=Math.max(1,cnt[b2]); if(pat[b2]>max)max=pat[b2]; if(pat[b2]<min)min=pat[b2]; sum+=pat[b2]; }
    var contrast=sum>0?(max-min)/(sum/m):0;
    if(contrast>best.score) best={beats:m, score:contrast};
  });
  var label=best.beats===2?'2/4':best.beats===3?'3/4':best.beats===6?'6/8':'4/4';
  var metroBeats=best.beats===6?2:best.beats;
  // fase do beat: offset o em [0,P) que maximiza onsets em k*P+o
  var bestO=0, bestS=-1;
  for(var o=0;o<Math.floor(P);o++){
    var s=0; for(var k=0;k*P+o<onset.length;k++) s+=Math.max(0, onset[Math.round(k*P+o)]);
    if(s>bestS){bestS=s;bestO=o;}
  }
  return {label:label, metroBeats:metroBeats, beatPeriodSec:60/bpm, beatPhaseSec:bestO*hopSec};
}

/* ---------- Melodia ---------- */
function extractMelody(x,sr){
  var hp=new Float32Array(x.length);
  for(var i=1;i<x.length;i++) hp[i]=x[i]-0.95*x[i-1];
  var N=2048, hop=1024, win=hann(N), fftN=4096;
  var re=new Float32Array(fftN), im=new Float32Array(fftN);
  var minLag=Math.round(sr/1400), maxLag=Math.round(sr/90);
  var seq=[];
  for(var start=0; start+N<=hp.length; start+=hop){
    for(i=0;i<fftN;i++){re[i]=0;im[i]=0;}
    for(i=0;i<N;i++) re[i]=hp[start+i]*win[i];
    fft(re,im);
    for(i=0;i<fftN;i++){ re[i]=re[i]*re[i]+im[i]*im[i]; im[i]=0; }
    fft(re,im);
    var r0=re[0]/fftN; if(r0<=0){seq.push(null);continue;}
    var bestK=-1, bestR=-1;
    for(var k=minLag;k<=maxLag&&k<fftN;k++){ var rk=re[k]/fftN; if(rk>bestR){bestR=rk;bestK=k;} }
    var conf=bestR/r0;
    if(conf>0.2 && bestK>0){
      var y0=re[bestK-1]/fftN, y1=bestR, y2=re[bestK+1]/fftN;
      var denom=(y0-2*y1+y2), kk=bestK;
      if(Math.abs(denom)>1e-12) kk=bestK+0.5*(y0-y2)/denom;
      var f=sr/kk;
      if(f>=80&&f<=1500){ var midi=Math.round(69+12*Math.log2(f/440)); seq.push({midi:midi}); }
      else seq.push(null);
    } else seq.push(null);
  }
  var hopSec=hop/sr, notes=[], cur=null;
  for(i=0;i<seq.length;i++){
    var t=i*hopSec, p=seq[i];
    if(p && cur && cur.midi===p.midi){ cur.dur+=hopSec; }
    else { if(cur && cur.dur>=0.12) notes.push(cur); cur=p?{midi:p.midi, start:t, dur:hopSec}:null; }
  }
  if(cur && cur.dur>=0.12) notes.push(cur);
  return notes;
}

/* ---------- Forma de onda ---------- */
function computeWaveform(x,points){
  var out=[], block=Math.max(1,Math.floor(x.length/points));
  for(var i=0;i<points;i++){
    var min=1,max=-1,st=i*block;
    for(var j=0;j<block&&st+j<x.length;j++){ var v=x[st+j]; if(v<min)min=v; if(v>max)max=v; }
    out.push([min,max]);
  }
  return out;
}

/* ---------- Render: waveform / piano roll ---------- */
function drawWaveform(){
  if(!analysis) return;
  var dpr=window.devicePixelRatio||1, w=waveCanvas.clientWidth||800, h=110;
  waveCanvas.width=w*dpr; waveCanvas.height=h*dpr;
  var ctx=waveCanvas.getContext('2d'); ctx.scale(dpr,dpr); ctx.clearRect(0,0,w,h);
  var wf=analysis.waveform, n=wf.length, bw=w/n;
  ctx.strokeStyle='rgba(161,161,168,.12)'; ctx.lineWidth=1;
  ctx.beginPath(); ctx.moveTo(0,h/2); ctx.lineTo(w,h/2); ctx.stroke();
  ctx.fillStyle='#7aac2b';
  for(var i=0;i<n;i++){
    var y1=(1-(wf[i][1]+1)/2)*h, y2=(1-(wf[i][0]+1)/2)*h;
    ctx.fillRect(i*bw, Math.min(y1,y2), Math.max(bw,0.6), Math.abs(y2-y1)||1);
  }
  var ratio=analysis.duration>0? getCurrentTime()/analysis.duration : 0;
  ctx.fillStyle='rgba(244,244,245,.85)'; ctx.fillRect(ratio*w-1,0,2,h);
}
function roundRect(ctx,x,y,w,h,r){
  ctx.beginPath(); ctx.moveTo(x+r,y);
  ctx.arcTo(x+w,y,x+w,y+h,r); ctx.arcTo(x+w,y+h,x,y+h,r);
  ctx.arcTo(x,y+h,x,y,r); ctx.arcTo(x,y,x+w,y,r); ctx.closePath();
}
function drawPianoRoll(){
  if(!analysis || !analysis.notes.length) return;
  var cv=$('pianoRoll'), dpr=window.devicePixelRatio||1, w=cv.clientWidth||800, h=220;
  cv.width=w*dpr; cv.height=h*dpr;
  var ctx=cv.getContext('2d'); ctx.scale(dpr,dpr); ctx.clearRect(0,0,w,h);
  var notes=analysis.notes, minMidi=Infinity, maxMidi=-Infinity;
  for(var i=0;i<notes.length;i++){ if(notes[i].midi<minMidi)minMidi=notes[i].midi; if(notes[i].midi>maxMidi)maxMidi=notes[i].midi; }
  minMidi-=2; maxMidi+=2; var range=Math.max(maxMidi-minMidi,12), dur=analysis.duration;
  ctx.strokeStyle='rgba(161,161,168,.1)'; ctx.lineWidth=1;
  for(var m=Math.ceil(minMidi/12)*12; m<=maxMidi; m+=12){
    var y=(1-(m-minMidi)/range)*h; ctx.beginPath(); ctx.moveTo(0,y); ctx.lineTo(w,y); ctx.stroke();
  }
  for(i=0;i<notes.length;i++){
    var nt=notes[i], x=(nt.start/dur)*w, rw=Math.max((nt.dur/dur)*w,2);
    var y2=(1-((nt.midi+transpose)-minMidi)/range)*h, rh=Math.max(h/range*0.7,3);
    var grad=ctx.createLinearGradient(0,y2-rh/2,0,y2+rh/2);
    grad.addColorStop(0,'#9cc94a'); grad.addColorStop(1,'#7aac2b');
    ctx.fillStyle=grad; roundRect(ctx,x,y2-rh/2,rw,rh,2); ctx.fill();
  }
  var t=getCurrentTime(), ratio=dur>0?t/dur:0;
  ctx.strokeStyle='#c4a87c'; ctx.lineWidth=1.5;
  ctx.beginPath(); ctx.moveTo(ratio*w,0); ctx.lineTo(ratio*w,h); ctx.stroke();
}

/* ---------- Teclado de piano ---------- */
function buildPianoKeys(){
  var c=$('pianoKeys'); c.innerHTML='';
  if(!analysis) return;
  var startMidi=60, octaves=2, totalWhite=octaves*7, kw=100/totalWhite;
  c.style.setProperty('--kw', kw+'%');
  var scaleSet={}; analysis.scaleNotes.forEach(function(s){scaleSet[mod12(s)]=true;});
  var rootPc=mod12(analysis.keyRoot+transpose);
  var whiteIdx=0;
  for(var m=startMidi; m<startMidi+12*octaves; m++){
    var pc=mod12(m), isBlack=[1,3,6,8,10].indexOf(pc)>=0;
    var inScale=!!scaleSet[pc], isRoot=pc===rootPc, label=dispNote(pc);
    if(!isBlack){
      var el=document.createElement('div');
      el.className='piano-white'+(inScale?' in-scale':'')+(isRoot?' is-root':'');
      el.style.left=(whiteIdx*kw)+'%';
      el.textContent=(inScale||isRoot)?label:'';
      c.appendChild(el); whiteIdx++;
    } else {
      var bel=document.createElement('div');
      bel.className='piano-black'+(inScale?' in-scale':'')+(isRoot?' is-root':'');
      bel.style.left=(whiteIdx*kw - kw*0.31)+'%';
      bel.textContent=(inScale||isRoot)?label:'';
      c.appendChild(bel);
    }
  }
}

/* ---------- Beat dots ---------- */
function buildBeatDots(){
  beatDots.innerHTML='';
  for(var i=0;i<metro.beatsPerBar;i++){
    var d=document.createElement('div');
    d.className='beat-dot'+(i===0?' accent':'');
    beatDots.appendChild(d);
  }
}

/* ---------- Render principal ---------- */
function renderResults(){
  $('statBpm').textContent=analysis.bpm;
  var root=mod12(analysis.keyRoot+transpose);
  var modePt=analysis.keyMode==='major'?'maior':'menor';
  $('statKey').textContent=dispNote(root)+' '+modePt;
  $('statKeySub').textContent=SOLFEGE[root]+' '+modePt+' — '+(analysis.keyMode==='major'?'campo maior':'campo menor');
  $('statMeter').textContent=analysis.meter.label;
  $('statMeterSub').textContent='compasso estimado';
  $('statDur').textContent=fmtTime(analysis.duration);

  var sc=$('statScale'); sc.innerHTML='';
  analysis.scaleNotes.forEach(function(s,idx){
    var c=document.createElement('span');
    c.className='scale-chip'+(idx===0?' root':'');
    c.textContent=dispNoteT(s); sc.appendChild(c);
  });
  $('scaleHint').textContent='Escala '+(analysis.keyMode==='major'?'maior':'menor')+' natural — tônica em destaque';

  var ct=$('chordTimeline'); ct.innerHTML='';
  analysis.chords.forEach(function(ch,idx){
    var el=document.createElement('div'); el.className='chord-chip'; el.dataset.idx=idx;
    var name=ch.rootIdx<0?'—':dispNoteT(ch.rootIdx)+ch.suffix;
    var deg=ch.rootIdx<0?'—':chordDegree(ch, analysis.keyRoot, analysis.keyMode);
    el.innerHTML='<div class="chord-name">'+name+'</div>'+
                 '<div class="chord-degree">'+deg+'</div>'+
                 '<div class="chord-time">'+fmtTime(ch.time)+'</div>'+
                 '<div class="chord-dur">'+ch.dur.toFixed(1)+'s</div>';
    el.addEventListener('click', function(){ seek(ch.time); play(); });
    ct.appendChild(el);
  });
  $('chordCount').textContent=analysis.chords.length+' acorde(s)';

  var nl=$('noteList'); nl.innerHTML='';
  analysis.notes.slice(0,300).forEach(function(nt){
    var p=document.createElement('span'); p.className='note-pill';
    p.innerHTML=midiToName(nt.midi)+'<span class="nt">'+fmtTime(nt.start)+'</span>';
    p.addEventListener('click', function(){ seek(nt.start); play(); });
    nl.appendChild(p);
  });
  $('noteCount').textContent=analysis.notes.length+' nota(s) estimada(s)';

  buildPianoKeys();
  results.classList.remove('hidden');
  adjustBar.classList.remove('hidden');
  pdfBtn.classList.remove('hidden'); wavBtn.classList.remove('hidden');
  metroBpm.textContent=analysis.bpm+' BPM · '+analysis.meter.label;
  buildBeatDots();
  if(window.lucide) lucide.createIcons();
  drawWaveform(); drawPianoRoll();
}

/* ---------- Playback ---------- */
function ensureCtx(){
  if(!audioCtx){
    var AC=window.AudioContext||window.webkitAudioContext;
    audioCtx=new AC();
    masterGain=audioCtx.createGain(); masterGain.gain.value=parseFloat(volume.value);
    masterGain.connect(audioCtx.destination);
    metroGain=audioCtx.createGain(); metroGain.gain.value=0.5; metroGain.connect(audioCtx.destination);
  }
  if(audioCtx.state==='suspended') audioCtx.resume();
}
function getCurrentTime(){
  if(!pb.playing) return pb.offset;
  return pb.offset + (audioCtx.currentTime-pb.startedAt)*pb.rate;
}
function stopSource(){
  if(pb.source){ try{pb.source.onended=null; pb.source.stop();}catch(e){} pb.source.disconnect(); pb.source=null; }
}
function play(){
  if(!audioBuffer) return;
  ensureCtx();
  if(pb.offset>=audioBuffer.duration-0.05) pb.offset=0;
  stopSource();
  var src=audioCtx.createBufferSource();
  src.buffer=audioBuffer;
  pb.rate=transposeRate();
  src.playbackRate.value=pb.rate;
  src.connect(masterGain);
  src.start(0, pb.offset);
  src.onended=function(){
    if(pb.playing && getCurrentTime()>=audioBuffer.duration-0.1){
      pb.playing=false; pb.offset=0; updatePlayIcon(); drawWaveform(); drawPianoRoll();
    }
  };
  pb.source=src; pb.startedAt=audioCtx.currentTime; pb.playing=true;
  updatePlayIcon(); cancelAnimationFrame(pb.raf); tick();
}
function pause(){
  if(!pb.playing) return;
  pb.offset=getCurrentTime(); stopSource(); pb.playing=false;
  cancelAnimationFrame(pb.raf); updatePlayIcon(); drawWaveform(); drawPianoRoll();
}
function seek(t){
  pb.offset=Math.max(0, Math.min(t, audioBuffer?audioBuffer.duration:0));
  if(!pb.playing){ curTime.textContent=fmtTime(pb.offset); drawWaveform(); drawPianoRoll(); }
}
function updatePlayIcon(){
  playBtn.innerHTML=pb.playing?'<i data-lucide="pause"></i>':'<i data-lucide="play"></i>';
  if(window.lucide) lucide.createIcons();
}
function tick(){
  if(!pb.playing) return;
  var t=getCurrentTime();
  curTime.textContent=fmtTime(t);
  if(analysis && analysis.chords){
    var idx=-1;
    for(var i=0;i<analysis.chords.length;i++){
      if(t>=analysis.chords[i].time && t<analysis.chords[i].time+analysis.chords[i].dur) idx=i;
    }
    if(idx!==pb.lastChordIdx){
      pb.lastChordIdx=idx;
      var chips=document.querySelectorAll('.chord-chip');
      chips.forEach(function(c,ci){ c.classList.toggle('active', ci===idx); });
      if(idx>=0 && chips[idx]) chips[idx].scrollIntoView({behavior:'smooth', inline:'center', block:'nearest'});
    }
  }
  drawWaveform(); drawPianoRoll();
  pb.raf=requestAnimationFrame(tick);
}

/* ---------- Metrônomo ---------- */
function scheduleClick(time, accent){
  var osc=audioCtx.createOscillator(), g=audioCtx.createGain();
  osc.type='sine'; osc.frequency.value=accent?1320:880;
  g.gain.setValueAtTime(accent?0.5:0.32, time);
  g.gain.exponentialRampToValueAtTime(0.001, time+0.06);
  osc.connect(g); g.connect(metroGain);
  osc.start(time); osc.stop(time+0.07);
}
function metroScheduler(){
  while(metro.nextTime < audioCtx.currentTime + 0.12){
    scheduleClick(metro.nextTime, metro.beat % metro.beatsPerBar === 0);
    metro.nextTime += analysis.meter.beatPeriodSec;
    metro.beat++;
  }
}
function metroDotLoop(){
  if(!metro.on) return;
  var now=audioCtx.currentTime, P=analysis.meter.beatPeriodSec, ph=analysis.meter.beatPhaseSec;
  var idx=Math.floor((now-ph)/P) % metro.beatsPerBar;
  if(idx<0) idx+=metro.beatsPerBar;
  var dots=beatDots.querySelectorAll('.beat-dot');
  dots.forEach(function(d,i){ d.classList.toggle('on', i===idx && now>=ph); });
  metro.raf=requestAnimationFrame(metroDotLoop);
}
function startMetro(){
  if(!analysis) return;
  ensureCtx();
  var now=audioCtx.currentTime, P=analysis.meter.beatPeriodSec, ph=analysis.meter.beatPhaseSec;
  metro.nextTime=ph + Math.ceil((now-ph)/P)*P;
  if(metro.nextTime - now > P) metro.nextTime -= P;
  metro.beat=Math.round((metro.nextTime - ph)/P);
  metro.timer=setInterval(metroScheduler, 25);
  metro.on=true;
  metroBtn.classList.add('active');
  metroBtn.innerHTML='<i data-lucide="square"></i><span>Parar</span>';
  if(window.lucide) lucide.createIcons();
  cancelAnimationFrame(metro.raf); metroDotLoop();
}
function stopMetro(){
  clearInterval(metro.timer); metro.on=false; cancelAnimationFrame(metro.raf);
  var dots=beatDots.querySelectorAll('.beat-dot');
  dots.forEach(function(d){ d.classList.remove('on'); });
  metroBtn.classList.remove('active');
  metroBtn.innerHTML='<i data-lucide="play"></i><span>Ativar</span>';
  if(window.lucide) lucide.createIcons();
}

/* ---------- Transposição ---------- */
function updateTransposeLabel(){
  var t=transpose;
  if(t===0) transposeLabel.textContent='Tom original';
  else{
    var abs=Math.abs(t), toms=(abs/2).toFixed(1).replace('.0','');
    var dir=t>0?'+':'−';
    var extra=abs%12===0? ' ('+dir+(abs/12)+' oitava'+(abs/12>1?'s':'')+')':'';
    transposeLabel.textContent=dir+abs+' semitom'+(abs>1?'s':'')+' ('+dir+toms+' tom'+(toms!=='1'?'s':'')+')'+extra;
  }
  transposeSlider.value=t;
}
function applyTranspose(newT){
  transpose=Math.max(-12, Math.min(12, newT));
  updateTransposeLabel();
  if(!analysis) return;
  var wasPlaying=pb.playing;
  if(wasPlaying) pause();
  renderResults();
  if(wasPlaying) play();
}

/* ---------- WAV export (áudio transposto) ---------- */
function encodeWAV(renderedBuffer, srOut){
  var ch=renderedBuffer.numberOfChannels, len=renderedBuffer.length;
  var data=renderedBuffer.getChannelData(0);
  var interleaved=new Float32Array(len*ch);
  for(var c=0;c<ch;c++){ var cd=renderedBuffer.getChannelData(c);
    for(var i=0;i<len;i++) interleaved[i*ch+c]=cd[i]; }
  var bytes=interleaved.length*2, buffer=new ArrayBuffer(44+bytes), view=new DataView(buffer);
  function ws(o,s){ for(var i=0;i<s.length;i++) view.setUint8(o+i, s.charCodeAt(i)); }
  ws(0,'RIFF'); view.setUint32(4,36+bytes,true); ws(8,'WAVE');
  ws(12,'fmt '); view.setUint32(16,16,true); view.setUint16(20,1,true); view.setUint16(22,ch,true);
  view.setUint32(24,srOut,true); view.setUint32(28,srOut*ch*2,true); view.setUint16(32,ch*2,true); view.setUint16(34,16,true);
  ws(36,'data'); view.setUint32(40,bytes,true);
  var off=44;
  for(i=0;i<interleaved.length;i++,off+=2){ var s=Math.max(-1,Math.min(1,interleaved[i])); view.setInt16(off, s<0?s*0x8000:s*0x7FFF, true); }
  return new Blob([buffer], {type:'audio/wav'});
}
async function exportWAV(){
  if(!audioBuffer) return;
  wavBtn.disabled=true; var orig=wavBtn.querySelector('span').textContent;
  wavBtn.querySelector('span').textContent='Renderizando…';
  try{
    var rate=transposeRate(), srOut=44100, ch=2;
    var dur=audioBuffer.duration/rate;
    var off=new (window.OfflineAudioContext||window.webkitOfflineAudioContext)(ch, Math.ceil(dur*srOut), srOut);
    var src=off.createBufferSource(); src.buffer=audioBuffer; src.playbackRate.value=rate;
    src.connect(off.destination); src.start();
    var rb=await off.startRendering();
    var blob=encodeWAV(rb, srOut);
    var a=document.createElement('a');
    a.href=URL.createObjectURL(blob);
    var t=transpose===0?'original':(transpose>0?'+':'')+transpose+'st';
    a.download='audio-'+t+'.wav'; a.click();
    setTimeout(function(){ URL.revokeObjectURL(a.href); }, 2000);
    showToast('Áudio WAV exportado no tom selecionado.');
  }catch(e){ showToast('Erro ao renderizar WAV: '+e.message); }
  wavBtn.disabled=false; wavBtn.querySelector('span').textContent=orig;
}

/* ---------- PDF profissional ---------- */
function exportPDF(){
  if(!analysis || !window.jspdf) return;
  try{
    var jsPDF=window.jspdf.jsPDF;
    var doc=new jsPDF({unit:'mm', format:'a4'});
    var W=210, M=14, cw=W-2*M, y=0;
    var DARK=[31,31,33], ACC=[122,172,43], ACC2=[196,168,124], GRAY=[110,110,115], LGRAY=[235,235,237];

    function newPage(){ doc.addPage(); y=M; headerBand(false); }
    function headerBand(first){
      doc.setFillColor(DARK[0],DARK[1],DARK[2]); doc.rect(0,0,W,24,'F');
      doc.setFillColor(ACC[0],ACC[1],ACC[2]); doc.rect(0,24,W,1.2,'F');
      doc.setTextColor(255,255,255); doc.setFont('helvetica','bold'); doc.setFontSize(17);
      doc.text('ANALISE MUSICAL PRO', M, 11);
      doc.setFont('helvetica','normal'); doc.setFontSize(9); doc.setTextColor(ACC2[0],ACC2[1],ACC2[2]);
      var tn=trackName.textContent||'música importada';
      if(tn.length>55) tn=tn.substring(0,55)+'…';
      doc.text(tn, M, 17.5);
      doc.setTextColor(180,180,180); doc.setFontSize(8);
      doc.text('Acordes · Notas · Escala · BPM · Compasso · Transposicao', M, 21.5);
      y=32;
    }
    function sectionTitle(txt){
      if(y>265) newPage();
      doc.setFillColor(ACC[0],ACC[1],ACC[2]); doc.rect(M,y,1.6,5,'F');
      doc.setTextColor(DARK[0],DARK[1],DARK[2]); doc.setFont('helvetica','bold'); doc.setFontSize(12);
      doc.text(txt, M+4, y+4.2); y+=8;
    }
    headerBand(true);

    // Caixas de stats
    var boxes=[
      ['BPM', String(analysis.bpm)],
      ['TONALIDADE', dispNote(mod12(analysis.keyRoot+transpose))+' '+(analysis.keyMode==='major'?'maior':'menor')],
      ['COMPASSO', analysis.meter.label],
      ['DURACAO', fmtTime(analysis.duration)]
    ];
    var bw=(cw-3*4)/4, bx=M;
    boxes.forEach(function(b){
      doc.setDrawColor(210,210,212); doc.setFillColor(LGRAY[0],LGRAY[1],LGRAY[2]);
      doc.roundedRect(bx,y,bw,18,2,2,'FD');
      doc.setTextColor(GRAY[0],GRAY[1],GRAY[2]); doc.setFont('helvetica','bold'); doc.setFontSize(7);
      doc.text(b[0], bx+3, y+6);
      doc.setTextColor(DARK[0],DARK[1],DARK[2]); doc.setFont('helvetica','bold'); doc.setFontSize(14);
      doc.text(b[1], bx+3, y+13.5);
      bx+=bw+4;
    });
    y+=26;
    if(transpose!==0){
      doc.setFillColor(ACC2[0],ACC2[1],ACC2[2]); doc.roundedRect(M,y,cw,7,1.5,1.5,'F');
      doc.setTextColor(40,30,10); doc.setFont('helvetica','bold'); doc.setFontSize(9);
      doc.text('Transposicao aplicada: '+(transpose>0?'+':'')+transpose+' semitons (audio e notacao)', M+3, y+4.7);
      y+=11;
    }

    // Escala
    sectionTitle('Escala e campo harmonico');
    var sn=analysis.scaleNotes, step=cw/7;
    for(var i=0;i<7;i++){
      var cx=M+i*step+step/2;
      doc.setFillColor(i===0?ACC2[0]:ACC[0], i===0?ACC2[1]:ACC[1], i===0?ACC2[2]:ACC[2]);
      doc.circle(cx, y+5, 5.5, 'F');
      doc.setTextColor(255,255,255); doc.setFont('helvetica','bold'); doc.setFontSize(10);
      doc.text(dispNoteT(sn[i]), cx, y+6.5, {align:'center'});
      doc.setTextColor(GRAY[0],GRAY[1],GRAY[2]); doc.setFont('helvetica','normal'); doc.setFontSize(7);
      doc.text(['I','II','III','IV','V','VI','VII'][i], cx, y+13, {align:'center'});
    }
    y+=20;

    // Acordes (tabela)
    sectionTitle('Progressao de acordes ('+analysis.chords.length+')');
    var cols=[10, 22, 40, 28, cw-10-22-40-28];
    var colX=[M, M+cols[0], M+cols[0]+cols[1], M+cols[0]+cols[1]+cols[2], M+cols[0]+cols[1]+cols[2]+cols[3]];
    function chordRow(n, tempo, acorde, grau, dur, head){
      if(y>270) newPage();
      if(head){ doc.setFillColor(DARK[0],DARK[1],DARK[2]); doc.rect(M,y-4.5,cw,6,'F'); doc.setTextColor(255,255,255); }
      else { doc.setFillColor(LGRAY[0],LGRAY[1],LGRAY[2]); if(n%2===0) doc.rect(M,y-4.5,cw,6,'F'); doc.setTextColor(DARK[0],DARK[1],DARK[2]); }
      doc.setFont('helvetica', head?'bold':'normal'); doc.setFontSize(8.5);
      doc.text(String(n), colX[0]+1, y);
      doc.text(tempo, colX[1]+1, y);
      doc.setFont('helvetica','bold'); doc.text(acorde, colX[2]+1, y);
      doc.setTextColor(140,100,40); doc.text(grau, colX[3]+1, y);
      doc.setTextColor(head?255:DARK[0], head?255:DARK[1], head?255:DARK[2]);
      doc.setFont('helvetica','normal'); doc.text(dur, colX[4]+1, y);
      y+=6.5;
    }
    chordRow('#','Tempo','Acorde','Grau','Duracao', true);
    analysis.chords.forEach(function(ch, i){
      var name=ch.rootIdx<0?'—':dispNoteT(ch.rootIdx)+ch.suffix;
      var deg=ch.rootIdx<0?'—':chordDegree(ch, analysis.keyRoot, analysis.keyMode);
      chordRow(i+1, fmtTime(ch.time), name, deg, ch.dur.toFixed(1)+'s', false);
    });
    y+=4;

    // Melodia (tabela, até 60 notas por página)
    sectionTitle('Melodia estimada (primeiras 80 notas)');
    var mcols=[16, 40, cw-16-40];
    var mx=[M, M+mcols[0], M+mcols[0]+mcols[1]];
    function noteRow(tempo, nota, dur, head){
      if(y>270) newPage();
      if(head){ doc.setFillColor(DARK[0],DARK[1],DARK[2]); doc.rect(M,y-4.5,cw,6,'F'); doc.setTextColor(255,255,255); }
      else { doc.setFillColor(LGRAY[0],LGRAY[1],LGRAY[2]); if(Math.floor(y)%2===0) doc.rect(M,y-4.5,cw,6,'F'); doc.setTextColor(DARK[0],DARK[1],DARK[2]); }
      doc.setFont('helvetica', head?'bold':'normal'); doc.setFontSize(8.5);
      doc.text(tempo, mx[0]+1, y);
      doc.setFont('helvetica','bold'); doc.text(nota, mx[1]+1, y);
      doc.setFont('helvetica','normal'); doc.text(dur, mx[2]+1, y);
      y+=6.5;
    }
    noteRow('Tempo','Nota','Duracao', true);
    analysis.notes.slice(0,80).forEach(function(nt){
      noteRow(fmtTime(nt.start), midiToName(nt.midi), nt.dur.toFixed(2)+'s', false);
    });

    // Rodapé em todas as páginas
    var pages=doc.getNumberOfPages();
    for(var p=1;p<=pages;p++){
      doc.setPage(p);
      doc.setDrawColor(210,210,212); doc.line(M, 285, W-M, 285);
      doc.setTextColor(GRAY[0],GRAY[1],GRAY[2]); doc.setFont('helvetica','normal'); doc.setFontSize(7.5);
      doc.text('Gerado por Analisador Musical PRO — analise local (Web Audio API). Valores estimados para apoio ao estudo.', M, 290);
      doc.text('Pagina '+p+'/'+pages, W-M, 290, {align:'right'});
    }
    doc.save('analise-musical-pro.pdf');
    showToast('PDF profissional exportado.');
  }catch(e){ console.error(e); showToast('Erro ao gerar PDF: '+e.message); }
}

/* ---------- Pipeline de análise ---------- */
function setProgress(text,pct){ progressBox.classList.remove('hidden'); progressText.textContent=text; progressBar.style.width=(pct||0)+'%'; }
function showToast(msg){ toast.textContent=msg; toast.classList.remove('hidden'); clearTimeout(showToast._t); showToast._t=setTimeout(function(){toast.classList.add('hidden');},5000); }
function nextFrame(){ return new Promise(function(r){setTimeout(r,30);}); }

async function analyze(){
  try{
    setProgress('Reamostrando audio…',5); await nextFrame();
    var res=await toMono(audioBuffer); mono=res.data; sr=res.sr;
    analysis={duration:audioBuffer.duration};

    setProgress('Forma de onda…',12); await nextFrame();
    analysis.waveform=computeWaveform(mono,1600);
    totTime.textContent=fmtTime(audioBuffer.duration); drawWaveform();

    setProgress('Cromagrama (FFT)…',25); await nextFrame();
    var chroma=computeChromagram(mono,sr);

    setProgress('Tonalidade e escala…',42); await nextFrame();
    var g=new Float32Array(12), i,c;
    for(i=0;i<chroma.frames.length;i++) for(c=0;c<12;c++) g[c]+=chroma.frames[i][c];
    for(c=0;c<12;c++) g[c]/=chroma.frames.length;
    var key=findKey(g);
    analysis.keyRoot=key.root; analysis.keyMode=key.mode;
    analysis.scaleNotes=scaleNotes(key.root, key.mode);

    setProgress('Acordes…',58); await nextFrame();
    analysis.chords=findChords(chroma);

    setProgress('BPM e onsets…',72); await nextFrame();
    var bpmRes=findBPM(mono,sr); analysis.bpm=bpmRes.bpm;

    setProgress('Compasso…',80); await nextFrame();
    analysis.meter=estimateMeter(bpmRes.onset, bpmRes.hopSec, bpmRes.bpm);
    metro.beatsPerBar=analysis.meter.metroBeats;

    setProgress('Melodia (pitch detection)…',90); await nextFrame();
    analysis.notes=extractMelody(mono,sr);

    setProgress('Finalizando…',100); await nextFrame();
    progressBox.classList.add('hidden');
    renderResults();
    results.scrollIntoView({behavior:'smooth', block:'start'});
  }catch(err){
    console.error(err); progressBox.classList.add('hidden');
    showToast('Erro na analise: '+err.message);
  }
}

/* ---------- Carregamento ---------- */
async function loadArrayBuffer(buf, name){
  ensureCtx();
  try{ audioBuffer=await audioCtx.decodeAudioData(buf.slice(0)); }
  catch(e){ showToast('Nao foi possivel decodificar este audio. Formato nao suportado.'); return; }
  trackName.textContent=name;
  playerSection.classList.remove('hidden');
  pb.offset=0; pb.playing=false; pb.rate=1; pb.lastChordIdx=-1;
  if(metro.on) stopMetro();
  updatePlayIcon();
  playerSection.scrollIntoView({behavior:'smooth', block:'start'});
  analyze();
}
fileBtn.addEventListener('click', function(){ fileInput.click(); });
fileInput.addEventListener('change', function(){
  var f=fileInput.files[0]; if(!f) return;
  var r=new FileReader();
  r.onload=function(){ loadArrayBuffer(r.result, f.name); };
  r.onerror=function(){ showToast('Erro ao ler o arquivo.'); };
  r.readAsArrayBuffer(f);
});
urlBtn.addEventListener('click', async function(){
  var url=urlInput.value.trim();
  if(!url){ showToast('Cole um link de audio direto (https://…/musica.mp3).'); return; }
  setProgress('Baixando audio do link…',5);
  try{
    var resp=await fetch(url,{mode:'cors'});
    if(!resp.ok) throw new Error('HTTP '+resp.status);
    var buf=await resp.arrayBuffer();
    progressBox.classList.add('hidden');
    loadArrayBuffer(buf, url.split('/').pop().split('?')[0]||'link de audio');
  }catch(e){
    progressBox.classList.add('hidden');
    showToast('Link nao carregado (CORS). YouTube/Spotify nao funcionam — baixe o audio como arquivo.');
  }
});
['dragenter','dragover'].forEach(function(ev){ dropZone.addEventListener(ev,function(e){e.preventDefault();dropZone.classList.add('dragover');}); });
['dragleave','drop'].forEach(function(ev){ dropZone.addEventListener(ev,function(e){e.preventDefault();dropZone.classList.remove('dragover');}); });
dropZone.addEventListener('drop', function(e){
  var f=e.dataTransfer.files[0]; if(!f) return;
  var r=new FileReader(); r.onload=function(){loadArrayBuffer(r.result, f.name);}; r.readAsArrayBuffer(f);
});

/* ---------- Controles ---------- */
playBtn.addEventListener('click', function(){ pb.playing?pause():play(); });
stopBtn.addEventListener('click', function(){ pause(); seek(0); });
volume.addEventListener('input', function(){ if(masterGain) masterGain.gain.value=parseFloat(volume.value); });
function canvasSeek(cv,e){ if(!audioBuffer)return; var r=cv.getBoundingClientRect(); seek((e.clientX-r.left)/r.width*audioBuffer.duration); }
waveCanvas.addEventListener('click', function(e){ canvasSeek(waveCanvas,e); });
var pr=$('pianoRoll'); if(pr) pr.addEventListener('click', function(e){ canvasSeek(pr,e); });

solfegeBtn.addEventListener('click', function(){
  useSolfege=!useSolfege; solfegeBtn.classList.toggle('solfege', useSolfege);
  if(analysis) renderResults();
});
metroBtn.addEventListener('click', function(){ metro.on? stopMetro() : startMetro(); });

transposeSlider.addEventListener('input', function(){ applyTranspose(parseInt(transposeSlider.value,10)); });
document.querySelectorAll('.t-btn[data-t]').forEach(function(b){
  b.addEventListener('click', function(){ applyTranspose(transpose+parseInt(b.dataset.t,10)); });
});
transposeReset.addEventListener('click', function(){ applyTranspose(0); });

pdfBtn.addEventListener('click', exportPDF);
wavBtn.addEventListener('click', exportWAV);

window.addEventListener('resize', function(){ if(analysis){ drawWaveform(); drawPianoRoll(); } });
if(window.lucide) lucide.createIcons();
updateTransposeLabel();

})();
