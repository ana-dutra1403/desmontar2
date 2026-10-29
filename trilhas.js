/* DesmontAR 2.0 — trilhas de aprendizagem em realidade aumentada
 * Equipe: Ana Luísa, Ana Roberta, Giovanna e Luiza (UFPB)
 * Mapa de trilhas no estilo Duolingo, fases curtas com estrelas e RA com o mesmo marcador do DesmontAR. */
(function(){
const $=s=>document.querySelector(s);
const PI=Math.PI;
const reduceMotion=matchMedia('(prefers-reduced-motion: reduce)').matches;

/* ---------- cena 3D ---------- */
const renderer=new THREE.WebGLRenderer({antialias:true,alpha:true});
renderer.setPixelRatio(Math.min(devicePixelRatio||1,2));renderer.outputEncoding=THREE.sRGBEncoding;
renderer.toneMapping=THREE.ACESFilmicToneMapping;renderer.toneMappingExposure=1.05;
renderer.shadowMap.enabled=true;renderer.shadowMap.type=THREE.PCFSoftShadowMap;
$('#stage').appendChild(renderer.domElement);
const scene=new THREE.Scene();const BG=new THREE.Color(0x1b2330);scene.background=BG;
const camera=new THREE.PerspectiveCamera(45,1,.05,100);
const controls=new THREE.OrbitControls(camera,renderer.domElement);
controls.enableDamping=true;controls.maxPolarAngle=1.32;controls.minDistance=2.2;controls.maxDistance=11;controls.enablePan=false;
/* reflexos: um "estúdio" simples vira mapa de ambiente, para metal e plástico brilharem de verdade */
(function(){const pm=new THREE.PMREMGenerator(renderer);const es=new THREE.Scene();
  es.add(new THREE.Mesh(new THREE.BoxGeometry(30,14,30),new THREE.MeshBasicMaterial({color:0x2a3038,side:THREE.BackSide})));
  const panel=(w,h,c,x,y,z,ry,rx)=>{const m=new THREE.Mesh(new THREE.PlaneGeometry(w,h),new THREE.MeshBasicMaterial({color:c,side:THREE.DoubleSide}));m.position.set(x,y,z);m.rotation.set(rx||0,ry||0,0);es.add(m);};
  panel(10,3,new THREE.Color(5,5,5.2),0,6.5,0,0,PI/2);panel(6,4,new THREE.Color(2.4,2.5,2.8),-12,3,0,PI/2);panel(6,4,new THREE.Color(2.2,2.1,2),12,3,-2,-PI/2);
  panel(8,3,new THREE.Color(1.4,1.5,1.7),0,3,-14);panel(30,30,new THREE.Color(.25,.22,.2),0,-6.9,0,0,PI/2);
  scene.environment=pm.fromScene(es,.04).texture;pm.dispose();})();
scene.add(new THREE.HemisphereLight(0xf4f7ff,0x30343c,.35));
const sun=new THREE.DirectionalLight(0xffffff,1.5);sun.position.set(2.5,7,3.5);sun.castShadow=true;
sun.shadow.mapSize.set(1024,1024);Object.assign(sun.shadow.camera,{left:-3.5,right:3.5,top:3.5,bottom:-3.5,near:1,far:20});sun.shadow.bias=-.0008;sun.shadow.normalBias=.02;sun.shadow.radius=4;scene.add(sun);
const video=$('#video');

/* ---------- marcador DesmontAR: mesmo detector do jogo original ---------- */
const CAM={on:false,seen:-1e9,cv:document.createElement('canvas'),fr:.8,tp:new THREE.Vector3(),tq:new THREE.Quaternion(),has:false,last:null,found:0,lastOk:0};
CAM.ctx=CAM.cv.getContext('2d',{willReadFrequently:true});
const cvG=new CV.Image(),cvT=new CV.Image(),cvB=[];
const MKBITS=(()=>{let s=3;const r=()=>{s=(s*9301+49297)%233280;return s/233280};const b=[];for(let y=0;y<8;y++)for(let x=0;x<8;x++)b.push(r()<.45?1:0);return b;})();
const mAW=new THREE.Matrix4().set(1,0,0,0, 0,0,-1,0, 0,1,0,0, 0,0,0,1);
function hsolve(A,b){const n=b.length;for(let i=0;i<n;i++){let p=i;for(let r=i+1;r<n;r++)if(Math.abs(A[r][i])>Math.abs(A[p][i]))p=r;[A[i],A[p]]=[A[p],A[i]];[b[i],b[p]]=[b[p],b[i]];
  if(Math.abs(A[i][i])<1e-12)return null;for(let r=i+1;r<n;r++){const k=A[r][i]/A[i][i];for(let c=i;c<n;c++)A[r][c]-=k*A[i][c];b[r]-=k*b[i];}}
  const x=new Array(n);for(let i=n-1;i>=0;i--){let v=b[i];for(let c=i+1;c<n;c++)v-=A[i][c]*x[c];x[i]=v/A[i][i];}return x;}
function homog(src,dst){const A=[],b=[];for(let i=0;i<4;i++){const [X,Y]=src[i],[x,y]=dst[i];A.push([X,Y,1,0,0,0,-x*X,-x*Y]);b.push(x);A.push([0,0,0,X,Y,1,-y*X,-y*Y]);b.push(y);}
  const h=hsolve(A,b);return h&&[[h[0],h[1],h[2]],[h[3],h[4],h[5]],[h[6],h[7],1]];}
const UNIT=[[0,0],[1,0],[1,1],[0,1]];
function hp(H,u,v){const w=H[2][0]*u+H[2][1]*v+H[2][2];return [(H[0][0]*u+H[0][1]*v+H[0][2])/w,(H[1][0]*u+H[1][1]*v+H[1][2])/w];}
function gAt(g,w,h,H,u,v){const [x,y]=hp(H,u,v);const xi=Math.round(x),yi=Math.round(y);if(xi<1||yi<1||xi>=w-1||yi>=h-1)return -1;
  const i=yi*w+xi;return (g[i]*2+g[i-1]+g[i+1]+g[i-w]+g[i+w]+g[i-w-1]+g[i-w+1]+g[i+w-1]+g[i+w+1])/10;}
function readMarker(g,w,h,c){
  const H=homog(UNIT,c.map(p=>[p.x,p.y]));if(!H)return null;
  let ring=0,nr=0,white=0,nw=0;
  for(let k=.08;k<.95;k+=.12)for(const [u,v] of [[k,.05],[k,.95],[.05,k],[.95,k]]){const q=gAt(g,w,h,H,u,v);if(q<0)return null;ring+=q;nr++;}
  for(const [u,v] of [[.15,.15],[.85,.15],[.15,.72],[.85,.72],[.5,.14],[.14,.5],[.86,.5]]){const q=gAt(g,w,h,H,u,v);if(q<0)return null;white+=q;nw++;}
  ring/=nr;white/=nw;if(white-ring<25)return null;const th=(ring+white)/2;
  let best=99,rot=0;
  for(let r=0;r<4;r++){const q=[c[r],c[(r+1)%4],c[(r+2)%4],c[(r+3)%4]];const Hr=homog(UNIT,q.map(p=>[p.x,p.y]));if(!Hr)continue;let d=0;
    for(let y=0;y<8&&d<=best;y++)for(let x=0;x<8;x++){const v=gAt(g,w,h,Hr,(116+40*x)/512,(116+40*y)/512);if(v<0){d=99;break;}if((v<th?1:0)!==MKBITS[y*8+x])d++;}
    if(d<best){best=d;rot=r;}}
  if(best>9)return null;
  return {q:[c[rot],c[(rot+1)%4],c[(rot+2)%4],c[(rot+3)%4]],d:best};}
/* refina os cantos: ajusta uma reta em cada lado do contorno e cruza as retas (precisão abaixo de 1 pixel) */
function refineCorners(q,ct){const L=[];
  for(let i=0;i<4;i++){const a=q[i],b=q[(i+1)%4],dx=b.x-a.x,dy=b.y-a.y,len=Math.hypot(dx,dy),ux=dx/len,uy=dy/len;
    let n=0,mx=0,my=0;const pts=[];for(const p of ct){const t=(p.x-a.x)*ux+(p.y-a.y)*uy,d=-(p.x-a.x)*uy+(p.y-a.y)*ux;if(t>len*.12&&t<len*.88&&Math.abs(d)<2.5){pts.push(p);mx+=p.x;my+=p.y;n++;}}
    if(n<6)return q;mx/=n;my/=n;let sxx=0,sxy=0,syy=0;for(const p of pts){const x=p.x-mx,y=p.y-my;sxx+=x*x;sxy+=x*y;syy+=y*y;}
    const th=.5*Math.atan2(2*sxy,sxx-syy);L.push([mx,my,Math.cos(th),Math.sin(th)]);}
  const out=[];for(let i=0;i<4;i++){const A=L[(i+3)%4],B=L[i];const den=A[2]*B[3]-A[3]*B[2];if(Math.abs(den)<1e-6)return q;
    const t=((B[0]-A[0])*B[3]-(B[1]-A[1])*B[2])/den;const x=A[0]+A[2]*t,y=A[1]+A[3]*t;if(Math.hypot(x-q[i].x,y-q[i].y)>4)return q;out.push({x,y});}
  return out;}
function poseFromCorners(q,w,h,f){
  const img=q.map(p=>[p.x-w/2,h/2-p.y]);const H=homog([[-1.5,1.5],[1.5,1.5],[1.5,-1.5],[-1.5,-1.5]],img);if(!H)return null;
  const col=j=>new THREE.Vector3(H[0][j]/f,H[1][j]/f,-H[2][j]);const h1=col(0),h2=col(1),h3=col(2);
  let l=2/(h1.length()+h2.length());if(h3.z*l>0)l=-l;
  const a=h1.multiplyScalar(l).normalize(),b=h2.multiplyScalar(l).normalize(),t=h3.multiplyScalar(l);
  const m=a.clone().add(b).normalize(),p=new THREE.Vector3().crossVectors(a,b).cross(m).normalize();
  const r1=m.clone().sub(p).normalize(),r2=m.clone().add(p).normalize();
  let R1=r1,R2=r2;if(r2.dot(a)>r1.dot(a)){R1=r2;R2=r1;}const R3=new THREE.Vector3().crossVectors(R1,R2);
  return new THREE.Matrix4().set(R1.x,R2.x,R3.x,t.x, R1.y,R2.y,R3.y,t.y, R1.z,R2.z,R3.z,t.z, 0,0,0,1).multiply(mAW).invert();}
function detectMarker(){
  const vw=video.videoWidth,vh=video.videoHeight;if(!vw||video.readyState<2)return null;
  const sc=480/Math.max(vw,vh),w=Math.round(vw*sc),h=Math.round(vh*sc);
  if(CAM.cv.width!==w||CAM.cv.height!==h){CAM.cv.width=w;CAM.cv.height=h;}
  CAM.ctx.drawImage(video,0,0,w,h);const img=CAM.ctx.getImageData(0,0,w,h);
  CV.grayscale(img,cvG);CV.adaptiveThreshold(cvG,cvT,3,6);
  const cont=CV.findContours(cvT,cvB);let found=null,bestD=99,bestP=0,fct=null;
  for(const ct of cont){if(ct.length<w*.1)continue;const p=CV.approxPolyDP(ct,ct.length*.05);
    if(p.length!==4||!CV.isContourConvex(p)||CV.minEdgeLength(p)<12)continue;
    const dx1=p[1].x-p[0].x,dy1=p[1].y-p[0].y,dx2=p[2].x-p[0].x,dy2=p[2].y-p[0].y;if(dx1*dy2-dy1*dx2<0){const s=p[1];p[1]=p[3];p[3]=s;}
    const r=readMarker(cvG.data,w,h,p);if(!r)continue;const pr=CV.perimeter(p);
    if(r.d<bestD||(r.d===bestD&&pr>bestP)){found=r.q;bestD=r.d;bestP=pr;fct=ct;}}
  if(!found)return null;found=refineCorners(found,fct);
  const M=poseFromCorners(found,w,h,CAM.fr*Math.max(w,h));if(!M)return null;
  const p=new THREE.Vector3(),q=new THREE.Quaternion(),s=new THREE.Vector3();M.decompose(p,q,s);if(p.y<.1||!isFinite(p.x))return null;
  CAM.tp.copy(p);CAM.tq.copy(q);CAM.last=found;return true;}
function camFov(){if(!CAM.on||!video.videoWidth)return;const vw=video.videoWidth,vh=video.videoHeight,s=Math.max(innerWidth/vw,innerHeight/vh);
  camera.fov=2*Math.atan(innerHeight/2/(CAM.fr*Math.max(vw,vh)*s))*180/PI;camera.updateProjectionMatrix();}
video.addEventListener('loadedmetadata',camFov);video.addEventListener('resize',camFov);
CAM.sp=new THREE.Vector3();CAM.sq=new THREE.Quaternion();CAM.uYaw=0;CAM.uScale=1;
const qUser=new THREE.Quaternion(),yAx=new THREE.Vector3(0,1,0);
function camStep(){if(!CAM.on)return;
  if(detectMarker()){CAM.seen=performance.now();CAM.found++;
    if(!CAM.has||performance.now()-CAM.lastOk>500){CAM.sp.copy(CAM.tp);CAM.sq.copy(CAM.tq);CAM.has=true;}
    CAM.lastOk=performance.now();}
  /* suavização: parado fica firme, movimento rápido acompanha */
  const dp=CAM.sp.distanceTo(CAM.tp)/Math.max(1,CAM.tp.length()*.15),da=CAM.sq.angleTo(CAM.tq);
  const k=Math.min(.85,Math.max(.07,dp/.5,da/.2));
  CAM.sp.lerp(CAM.tp,k);CAM.sq.slerp(CAM.tq,k);
  /* gestos: girar e dar zoom no modelo = mover a câmera virtual em volta do marcador */
  qUser.setFromAxisAngle(yAx,-CAM.uYaw);
  camera.position.copy(CAM.sp).multiplyScalar(1/CAM.uScale).applyQuaternion(qUser);
  camera.quaternion.copy(qUser).multiply(CAM.sq);camera.updateMatrixWorld();}
const gPts=new Map();let gStart=null;
renderer.domElement.addEventListener('pointerdown',e=>{if(!CAM.on)return;gPts.set(e.pointerId,[e.clientX,e.clientY]);gStart=null;});
addEventListener('pointermove',e=>{if(!CAM.on||!gPts.has(e.pointerId))return;gPts.set(e.pointerId,[e.clientX,e.clientY]);
  const P=[...gPts.values()];
  if(!gStart)gStart={yaw:CAM.uYaw,sc:CAM.uScale,p:P.map(p=>p.slice()),d:P.length>1?Math.hypot(P[0][0]-P[1][0],P[0][1]-P[1][1]):0,n:P.length};
  if(P.length!==gStart.n){gStart=null;return;}
  if(P.length===1)CAM.uYaw=gStart.yaw+(P[0][0]-gStart.p[0][0])*.012;
  else if(gStart.d>10)CAM.uScale=Math.max(.4,Math.min(3,gStart.sc*Math.hypot(P[0][0]-P[1][0],P[0][1]-P[1][1])/gStart.d));});
document.addEventListener('gesturestart',e=>e.preventDefault());
const gEnd=e=>{gPts.delete(e.pointerId);gStart=null;};addEventListener('pointerup',gEnd);addEventListener('pointercancel',gEnd);
/* abre a câmera com prazo: se o celular não responder, avisa em vez de ficar carregando para sempre */
const withT=(p,ms)=>Promise.race([p,new Promise((_,r)=>setTimeout(()=>r(new Error('timeout')),ms))]);
async function camOpen(){
  if(!navigator.mediaDevices||!navigator.mediaDevices.getUserMedia)return 'nosupport';
  try{if(video.srcObject){video.srcObject.getTracks().forEach(t=>t.stop());video.srcObject=null;}
    let st;try{st=await withT(navigator.mediaDevices.getUserMedia({video:{facingMode:{ideal:'environment'},width:{ideal:1280},height:{ideal:720}},audio:false}),15000);}
    catch(e){if(e&&e.name==='OverconstrainedError')st=await withT(navigator.mediaDevices.getUserMedia({video:true,audio:false}),15000);else throw e;}
    video.muted=true;video.setAttribute('playsinline','');video.setAttribute('muted','');video.srcObject=st;video.style.display='block';
    try{await withT(video.play(),4000);}catch(e){}
    await withT(new Promise(r=>{if(video.readyState>=1)r();else video.addEventListener('loadedmetadata',()=>r(),{once:true});}),6000);
    return 'ok';}
  catch(e){video.style.display='none';return e&&(e.name==='NotAllowedError'||e.name==='SecurityError')?'denied':e&&e.message==='timeout'?'timeout':e&&(e.name==='NotReadableError'||e.name==='AbortError')?'busy':'error';}}
const CAMERR={denied:'O celular não deu permissão para a câmera. No iPhone: Ajustes › Apps › Safari › Câmera › Permitir (ou toque em "aA" na barra do endereço › Ajustes do Site › Câmera). Depois recarregue a página.',
  timeout:'A câmera não respondeu. Feche os apps que podem estar usando a câmera (WhatsApp, chamadas de vídeo, Instagram), recarregue a página e tente de novo.',
  busy:'A câmera está ocupada por outro app. Feche chamadas de vídeo e apps de câmera e tente de novo.',
  nosupport:'Este navegador não libera a câmera. Abra o link direto no Safari (iPhone) ou no Chrome (Android), não por dentro do WhatsApp ou Instagram.',
  error:'Não consegui abrir a câmera. Recarregue a página e tente de novo.'};


/* ---------- utilidades ---------- */
const mat=(c,o={})=>new THREE.MeshStandardMaterial(Object.assign({color:c,roughness:.6,metalness:.05},o));
const METAL=o=>mat(0xc4c9d0,Object.assign({metalness:.9,roughness:.32},o));
const GOLD=()=>mat(0xd9ae4f,{metalness:.95,roughness:.28});
const PLASTIC=(c,o)=>mat(c,Object.assign({roughness:.45,metalness:0},o));
function box(w,h,d,c,o){return new THREE.Mesh(new THREE.BoxGeometry(w,h,d),c&&c.isMaterial?c:mat(c,o));}
/* caixa com cantos arredondados (extrusão com chanfro suave) */
const RGC={};
function rgeo(w,h,d,r){r=Math.max(.001,Math.min(r,w/2-.001,h/2-.001,d/2-.001));const k=[w,h,d,r].map(v=>v.toFixed(3)).join('_');if(RGC[k])return RGC[k];
  const sw=w-2*r,sh=h-2*r,s=new THREE.Shape();s.moveTo(-sw/2,-sh/2);s.lineTo(sw/2,-sh/2);s.lineTo(sw/2,sh/2);s.lineTo(-sw/2,sh/2);s.lineTo(-sw/2,-sh/2);
  const g=new THREE.ExtrudeGeometry(s,{depth:Math.max(.0005,d-2*r),bevelEnabled:true,bevelThickness:r,bevelSize:r,bevelSegments:3,curveSegments:4,steps:1});
  g.translate(0,0,-(d-2*r)/2);g.computeVertexNormals();return RGC[k]=g;}
function rbox(w,h,d,r,c,o){return new THREE.Mesh(rgeo(w,h,d,r),c&&c.isMaterial?c:mat(c,o));}
function cyl(r,h,c,o,seg=28){return new THREE.Mesh(new THREE.CylinderGeometry(r,r,h,seg),c&&c.isMaterial?c:mat(c,o));}
function at(m,x,y,z){m.position.set(x,y,z);return m;}
function rot(m,x,y,z){m.rotation.set(x||0,y||0,z||0);return m;}
const TEXC={};
function canvasTex(w,h,draw,key){if(key&&TEXC[key])return TEXC[key];const c=document.createElement('canvas');c.width=w;c.height=h;draw(c.getContext('2d'),w,h);const t=new THREE.CanvasTexture(c);t.encoding=THREE.sRGBEncoding;t.anisotropy=8;if(key)TEXC[key]=t;return t;}
/* adesivo/serigrafia: plano fino deitado em cima de uma peça */
function decal(w,d,tex,y,o={}){const m=new THREE.Mesh(new THREE.PlaneGeometry(w,d),new THREE.MeshStandardMaterial(Object.assign({map:tex,transparent:true,roughness:.6,metalness:0,polygonOffset:true,polygonOffsetFactor:-2},o)));m.rotation.x=-PI/2;m.position.y=y;return m;}
function face(w,h,tex,o={}){return new THREE.Mesh(new THREE.PlaneGeometry(w,h),new THREE.MeshStandardMaterial(Object.assign({map:tex,transparent:true,roughness:.5,metalness:0,polygonOffset:true,polygonOffsetFactor:-2},o)));}
function label(text,o={}){const fs=44,pad=18;const g0=document.createElement('canvas').getContext('2d');g0.font=`700 ${fs}px "Chakra Petch", Arial, sans-serif`;
  const tw=Math.ceil(g0.measureText(text).width)+pad*2,th=fs+pad;
  const tex=canvasTex(tw,th,(g,w,h)=>{g.fillStyle=o.bg||'rgba(20,26,34,.92)';const r=h/2;g.beginPath();g.moveTo(r,0);g.arcTo(w,0,w,h,r);g.arcTo(w,h,0,h,r);g.arcTo(0,h,0,0,r);g.arcTo(0,0,w,0,r);g.fill();
    g.font=`700 ${fs}px "Chakra Petch", Arial, sans-serif`;g.fillStyle=o.fg||'#fff';g.textAlign='center';g.textBaseline='middle';g.fillText(text,w/2,h/2+2);});
  const s=new THREE.Sprite(new THREE.SpriteMaterial({map:tex,depthTest:false,transparent:true,toneMapped:false}));const sz=o.size||.2;s.scale.set(sz*tw/th,sz,1);s.renderOrder=10;return s;}
const glowTex=canvasTex(128,128,(g,w,h)=>{const r=g.createRadialGradient(64,64,0,64,64,64);r.addColorStop(0,'rgba(255,255,255,1)');r.addColorStop(.35,'rgba(255,255,255,.45)');r.addColorStop(1,'rgba(255,255,255,0)');g.fillStyle=r;g.fillRect(0,0,w,h);});
function halo(color,s=.6){const h=new THREE.Sprite(new THREE.SpriteMaterial({map:glowTex,color,transparent:true,depthWrite:false,blending:THREE.AdditiveBlending,toneMapped:false}));h.scale.set(s,s,1);return h;}
function wire(pts,color,r=.018,tex){const curve=new THREE.CatmullRomCurve3(pts.map(p=>p.isVector3?p:new THREE.Vector3(...p)));
  const m=new THREE.Mesh(new THREE.TubeGeometry(curve,48,r,10,false),mat(color,{roughness:.42,map:tex||null}));m.userData.curve=curve;return m;}
/* fio com as duas pontas: arco suave entre dois pontos */
function arcWire(a,b,color,h=.35,r=.018){const A=new THREE.Vector3(...a),B=new THREE.Vector3(...b);const m1=A.clone().lerp(B,.25),m2=A.clone().lerp(B,.75);m1.y=Math.max(A.y,B.y)+h;m2.y=Math.max(A.y,B.y)+h;
  return wire([A,new THREE.Vector3(A.x,A.y+h*.4,A.z),m1,m2,new THREE.Vector3(B.x,B.y+h*.4,B.z),B],color,r);}
function txt(g,s,x,y,size,color='#fff',align='left',weight=700,font='Arial'){g.font=`${weight} ${size}px ${font}`;g.fillStyle=color;g.textAlign=align;g.textBaseline='middle';g.fillText(s,x,y);}
function rrect(g,x,y,w,h,r){g.beginPath();g.moveTo(x+r,y);g.arcTo(x+w,y,x+w,y+h,r);g.arcTo(x+w,y+h,x,y+h,r);g.arcTo(x,y+h,x,y,r);g.arcTo(x,y,x+w,y,r);g.closePath();}
/* trilhas de circuito impresso em um canvas */
function traces(g,w,h,n,col,seed=1){let s=seed;const r=()=>{s=(s*9301+49297)%233280;return s/233280;};g.strokeStyle=col;g.lineCap='round';
  for(let i=0;i<n;i++){g.lineWidth=1+r()*2.5;let x=r()*w,y=r()*h;g.beginPath();g.moveTo(x,y);for(let k=0;k<3;k++){if(r()<.5)x+=(r()-.5)*w*.5;else y+=(r()-.5)*h*.5;g.lineTo(x,y);}g.stroke();
    g.fillStyle=col;g.beginPath();g.arc(x,y,2.5,0,7);g.fill();}}


/* ---------- mesa e marcador (modo sem câmera) ---------- */
const env=new THREE.Group();scene.add(env);
const wood=canvasTex(1024,1024,(g,w,h)=>{const gr=g.createLinearGradient(0,0,w,0);gr.addColorStop(0,'#5a4330');gr.addColorStop(.5,'#644b36');gr.addColorStop(1,'#56402e');g.fillStyle=gr;g.fillRect(0,0,w,h);
  for(let i=0;i<220;i++){g.strokeStyle=`rgba(${25+Math.random()*30},${15+Math.random()*18},8,${.12+Math.random()*.2})`;g.lineWidth=.6+Math.random()*2.4;g.beginPath();const y=Math.random()*h;g.moveTo(0,y);g.bezierCurveTo(w*.3,y+Math.random()*24-12,w*.7,y+Math.random()*24-12,w,y+Math.random()*16-8);g.stroke();}
  for(let i=0;i<6;i++){g.strokeStyle='rgba(30,18,8,.25)';g.lineWidth=2;const x=Math.random()*w,y=Math.random()*h;for(let k=0;k<5;k++){g.beginPath();g.ellipse(x,y,18+k*9,6+k*3,0,0,7);g.stroke();}}});
wood.wrapS=wood.wrapT=THREE.RepeatWrapping;wood.repeat.set(2,2);
const table=new THREE.Mesh(new THREE.CircleGeometry(9,72),mat(0xffffff,{map:wood,roughness:.62}));table.rotation.x=-PI/2;table.position.y=-.006;table.receiveShadow=true;env.add(table);
const markerTex=canvasTex(512,512,(g,w,h)=>{g.fillStyle='#111';g.fillRect(0,0,w,h);g.fillStyle='#fff';g.fillRect(52,52,w-104,h-104);
  g.fillStyle='#111';for(let y=0;y<8;y++)for(let x=0;x<8;x++)if(MKBITS[y*8+x])g.fillRect(116+40*x-20,116+40*y-20,40,40);});
const markerPlane=new THREE.Mesh(new THREE.PlaneGeometry(3,3),new THREE.MeshStandardMaterial({map:markerTex,roughness:.85}));markerPlane.rotation.x=-PI/2;markerPlane.receiveShadow=true;env.add(markerPlane);
const paper=new THREE.Mesh(new THREE.PlaneGeometry(3.6,4.4),mat(0xf4f2ec,{roughness:.92}));paper.rotation.x=-PI/2;paper.position.set(0,-.003,.25);paper.receiveShadow=true;env.add(paper);
/* com a câmera: só a sombra das peças aparece sobre a mesa de verdade */
const shadowCatch=new THREE.Mesh(new THREE.PlaneGeometry(10,10),new THREE.ShadowMaterial({opacity:.32}));shadowCatch.rotation.x=-PI/2;shadowCatch.position.y=.001;shadowCatch.receiveShadow=true;shadowCatch.visible=false;scene.add(shadowCatch);

/* ---------- texturas compartilhadas ---------- */
const brushed=canvasTex(512,512,(g,w,h)=>{g.fillStyle='#c9ced5';g.fillRect(0,0,w,h);for(let i=0;i<1400;i++){g.strokeStyle=`rgba(${Math.random()<.5?255:90},${Math.random()<.5?255:95},${Math.random()<.5?255:105},${.04+Math.random()*.08})`;g.lineWidth=1;const y=Math.random()*h;g.beginPath();g.moveTo(0,y);g.lineTo(w,y+Math.random()*3-1.5);g.stroke();}},'brushed');
const BRUSHED=o=>mat(0xffffff,Object.assign({map:brushed,metalness:.85,roughness:.38},o));
const finsTex=canvasTex(256,64,(g,w,h)=>{for(let x=0;x<w;x+=16){const gr=g.createLinearGradient(x,0,x+16,0);gr.addColorStop(0,'#3a3f47');gr.addColorStop(.5,'#8c939d');gr.addColorStop(1,'#2a2e35');g.fillStyle=gr;g.fillRect(x,0,16,h);}},'fins');
function fan(r,blades,color=0x15181c,hubTex){const g=new THREE.Group();const bm=PLASTIC(color,{roughness:.5});
  for(let i=0;i<blades;i++){const b=new THREE.Mesh(new THREE.BoxGeometry(r*.78,.006,r*.42),bm);b.geometry.translate(r*.5,0,0);const p=new THREE.Group();b.rotation.x=.42;p.add(b);p.rotation.y=i*2*PI/blades;g.add(p);}
  const hub=cyl(r*.32,.03,PLASTIC(color,{roughness:.4}));g.add(hub);
  if(hubTex){const d=decal(r*.6,r*.6,hubTex,.016);g.add(d);}return g;}
const hubSticker=canvasTex(128,128,(g,w,h)=>{g.fillStyle='#14171c';g.beginPath();g.arc(64,64,64,0,7);g.fill();g.strokeStyle='#4aa8ff';g.lineWidth=6;g.beginPath();g.arc(64,64,44,0,7);g.stroke();txt(g,'D',64,66,52,'#e9eef5','center');},'hub');

/* ---------- peças de hardware ---------- */
function mkCPU(){const g=new THREE.Group();
  g.add(at(rbox(.44,.03,.44,.006,0x1f5e38,{roughness:.55}),0,0,0));
  for(let i=0;i<10;i++){const s=box(.022,.012,.012,i%2?0x8a6a3a:0xb9bec6,{metalness:.5});s.position.set(-.19+i*.042,.02,.2);g.add(s);}
  g.add(at(rbox(.37,.032,.37,.012,BRUSHED()),0,.03,0));
  const t=canvasTex(256,256,(c,w,h)=>{c.clearRect(0,0,w,h);txt(c,'DESMONT',128,70,34,'rgba(40,44,52,.75)','center',800);txt(c,'R7 · 8C/16T',128,118,24,'rgba(40,44,52,.65)','center',700);
    txt(c,'SOQUETE S5',128,156,20,'rgba(40,44,52,.6)','center',700);txt(c,'2026  BR',128,196,18,'rgba(40,44,52,.5)','center',600);c.strokeStyle='rgba(40,44,52,.35)';c.lineWidth=3;rrect(c,18,18,220,220,14);c.stroke();},'cpuTop');
  g.add(decal(.34,.34,t,.047,{metalness:.6,roughness:.4}));
  const tri=new THREE.Mesh(new THREE.ShapeGeometry(new THREE.Shape([new THREE.Vector2(0,0),new THREE.Vector2(.07,0),new THREE.Vector2(0,.07)])),mat(0xe0b44a,{metalness:.9,roughness:.25,side:THREE.DoubleSide}));
  tri.rotation.x=-PI/2;tri.position.set(-.215,.017,.215);g.add(tri);return g;}
function mkCooler(){const g=new THREE.Group();g.add(at(cyl(.21,.04,mat(0xc77b4a,{metalness:.9,roughness:.3})),0,0,0));
  const fins=new THREE.Group();const fm=mat(0xd2d6dc,{metalness:.8,roughness:.35});for(let i=0;i<19;i++)fins.add(at(box(.52,.17,.008,fm),0,.12,-.225+i*.025));g.add(fins);
  const shroud=new THREE.Mesh(new THREE.CylinderGeometry(.29,.29,.07,40,1,true),PLASTIC(0x16191e,{side:THREE.DoubleSide}));shroud.position.y=.27;g.add(shroud);
  const top=new THREE.Mesh(new THREE.RingGeometry(.27,.3,40),PLASTIC(0x16191e,{side:THREE.DoubleSide}));top.rotation.x=-PI/2;top.position.y=.305;g.add(top);
  const f=fan(.26,7,0x1c2026,hubSticker);f.position.y=.27;g.add(f);
  const ring=new THREE.Mesh(new THREE.TorusGeometry(.29,.012,8,48),mat(0x4aa8ff,{emissive:0x2a7fd6,emissiveIntensity:1.2}));ring.rotation.x=PI/2;ring.position.y=.306;g.add(ring);
  g.userData.fan=f;return g;}
function ramLabel(ddr5){return canvasTex(512,128,(c,w,h)=>{const gr=c.createLinearGradient(0,0,w,0);gr.addColorStop(0,'#2b3038');gr.addColorStop(1,'#3d434c');c.fillStyle=gr;c.fillRect(0,0,w,h);
  c.fillStyle='rgba(255,255,255,.06)';for(let i=0;i<8;i++){c.beginPath();c.moveTo(300+i*28,0);c.lineTo(260+i*28,h);c.lineTo(274+i*28,h);c.lineTo(314+i*28,0);c.fill();}
  txt(c,'DESMONT',30,40,30,'#e9eef5','left',800);txt(c,ddr5?'DDR5 · 16 GB · 6000 MHz':'DDR4 · 16 GB · 3200 MHz',30,86,24,ddr5?'#f5c518':'#9fd0ff','left',700);},ddr5?'ram5':'ram4');}
function mkRAM(lying,ddr5=true){const g=new THREE.Group();
  g.add(rbox(.02,.28,1.15,.004,0x1d6b45));
  const sp=mat(0x3a3f47,{metalness:.7,roughness:.35});
  for(const s of [-1,1]){g.add(at(rbox(.012,.25,1.13,.004,sp),s*.017,.025,0));const f=face(1.08,.23,ramLabel(ddr5),{metalness:.4,roughness:.4});f.position.set(s*.0235,.03,0);f.rotation.y=s*PI/2;g.add(f);}
  const rgb=rbox(.04,.028,1.1,.01,mat(ddr5?0x8a4fd1:0x2b62c9,{emissive:ddr5?0xb46cff:0x4aa8ff,emissiveIntensity:.45,roughness:.3}));rgb.position.y=.165;g.add(rgb);
  const nz=ddr5?-.02:.14;const gm=GOLD();g.add(at(box(.022,.04,(nz+.575)-.02,gm),0,-.13,(-.575+nz-.02)/2));g.add(at(box(.022,.04,(.575-nz)-.02,gm),0,-.13,(nz+.02+.575)/2));
  if(lying){g.rotation.z=PI/2;}return g;}
function mkGPU(){const g=new THREE.Group();
  g.add(at(rbox(1.4,.02,.52,.008,mat(0x2b2f36,{metalness:.7,roughness:.4})),0,-.055,0));
  g.add(at(box(1.34,.018,.5,0x14381f),0,-.035,0));
  g.add(at(rbox(1.42,.09,.55,.03,PLASTIC(0x23272e,{roughness:.4})),0,.015,0));
  const t=canvasTex(1024,400,(c,w,h)=>{c.clearRect(0,0,w,h);c.fillStyle='rgba(255,255,255,.05)';for(let i=0;i<6;i++){c.beginPath();c.moveTo(i*190,0);c.lineTo(i*190+120,h);c.lineTo(i*190+150,h);c.lineTo(i*190+30,0);c.fill();}
    c.strokeStyle='#f5c518';c.lineWidth=6;c.beginPath();c.moveTo(20,h-24);c.lineTo(w-20,h-24);c.stroke();txt(c,'DESMONT  GX 4070',w/2,h-60,30,'rgba(233,238,245,.8)','center',800);},'gpuTop');
  g.add(decal(1.38,.53,t,.061,{roughness:.4}));
  for(const x of [-.36,.36]){const ring=new THREE.Mesh(new THREE.TorusGeometry(.225,.018,8,48),PLASTIC(0x3a3f47));ring.rotation.x=PI/2;ring.position.set(x,.062,0);g.add(ring);
    const hole=new THREE.Mesh(new THREE.CircleGeometry(.215,40),PLASTIC(0x0c0e11));hole.rotation.x=-PI/2;hole.position.set(x,.0615,0);g.add(hole);
    const f=fan(.21,9,0x1a1d22,hubSticker);f.position.set(x,.068,0);g.add(f);(g.userData.fans=g.userData.fans||[]).push(f);}
  const br=at(box(.02,.16,.55,BRUSHED()),-.72,-.01,0);g.add(br);
  const ports=canvasTex(64,256,(c,w,h)=>{c.fillStyle='#c9ced5';c.fillRect(0,0,w,h);c.fillStyle='#16191e';[30,80,130,180].forEach(y=>rrect(c,14,y,36,30,5)||c.fill());},'gpuPorts');
  const pf=face(.5,.14,ports);pf.rotation.y=-PI/2;pf.rotation.z=PI/2;pf.position.set(-.731,-.01,0);g.add(pf);
  g.add(at(box(.8,.012,.06,GOLD()),-.05,-.058,.27));
  g.add(at(rbox(.16,.06,.09,.01,PLASTIC(0x111316)),.52,.07,-.2));return g;}
function mkSSD(){const g=new THREE.Group();g.add(rbox(.6,.012,.16,.004,0x111417));
  g.add(at(rbox(.14,.02,.12,.004,0x1b1e22),-.12,.012,0));g.add(at(rbox(.14,.02,.12,.004,0x1b1e22),.06,.012,0));
  const t=canvasTex(512,128,(c,w,h)=>{c.fillStyle='#eef1f5';rrect(c,0,0,w,h,10);c.fill();c.fillStyle='#2b62c9';c.fillRect(0,0,120,h);txt(c,'NVMe',60,64,34,'#fff','center',800);
    txt(c,'DESMONT SSD M.2',140,44,28,'#14181e','left',800);txt(c,'1 TB · PCIe 4.0',140,90,24,'#4b5563','left',700);},'ssd');
  g.add(decal(.42,.12,t,.024));g.add(at(box(.05,.012,.13,GOLD()),-.29,0,0));return g;}
function mkPSU(){const g=new THREE.Group();g.add(at(rbox(.85,.5,.85,.03,mat(0x1e2125,{roughness:.55,metalness:.3})),0,.25,0));
  const f=fan(.3,9,0x101215);f.position.y=.47;g.add(f);g.userData.fan=f;
  const grill=canvasTex(512,512,(c,w,h)=>{c.clearRect(0,0,w,h);c.fillStyle='#1b1e22';c.fillRect(0,0,w,h);
    c.fillStyle='#2b2f36';for(let y=40;y<h;y+=26)for(let x=40+(y/26%2)*13;x<w;x+=26){const d=Math.hypot(x-256,y-256);if(d<212){c.beginPath();for(let k=0;k<6;k++){const a=k*PI/3;c.lineTo(x+9*Math.cos(a),y+9*Math.sin(a));}c.closePath();c.globalCompositeOperation='destination-out';c.fill();c.globalCompositeOperation='source-over';}}
    c.strokeStyle='#2b2f36';c.lineWidth=8;c.beginPath();c.arc(256,256,214,0,7);c.stroke();},'psuGrill');
  g.add(decal(.8,.8,grill,.501,{metalness:.5,roughness:.4}));
  const lab=canvasTex(512,256,(c,w,h)=>{c.fillStyle='#e9eef5';rrect(c,0,0,w,h,12);c.fill();c.fillStyle='#d9ae4f';c.fillRect(0,0,w,56);txt(c,'80 PLUS GOLD',w/2,30,30,'#14181e','center',800);
    txt(c,'650 W',w/2,120,80,'#14181e','center',800);txt(c,'DESMONT PSU · 12 V · 5 V · 3,3 V',w/2,206,24,'#4b5563','center',700);},'psuLabel');
  const lf=face(.5,.25,lab);lf.position.set(0,.26,.426);g.add(lf);
  g.add(at(box(.08,.05,.03,0x111316),-.25,.38,-.43));g.add(at(box(.14,.1,.03,0x111316),.15,.3,-.43));return g;}

const RAMX={A1:.45,A2:.6,B1:.75,B2:.9};
const moboTex=canvasTex(960,1120,(c,w,h)=>{c.fillStyle='#1b1f24';c.fillRect(0,0,w,h);traces(c,w,h,240,'rgba(70,82,98,.55)',7);traces(c,w,h,80,'rgba(120,96,60,.35)',3);
  const U=x=>(x+1.2)/2.4*w,V=z=>(z+1.4)/2.8*h;
  c.fillStyle='#c9ced5';[[-1.12,-1.32],[1.12,-1.32],[-1.12,1.32],[1.12,1.32],[0.1,-.2],[1.12,.3]].forEach(([x,z])=>{c.beginPath();c.arc(U(x),V(z),14,0,7);c.fill();c.fillStyle='#1b1f24';c.beginPath();c.arc(U(x),V(z),7,0,7);c.fill();c.fillStyle='#c9ced5';});
  const S=(s,x,z,sz=20,a='center')=>txt(c,s,U(x),V(z),sz,'rgba(235,238,242,.85)',a,700);
  S('CPU',-.3,-.18);Object.entries(RAMX).forEach(([k,x])=>S('DDR5_'+k,x,.2,15));S('PCIE_1',-.35,.64,18);S('PCIE_2',-.85,1.0,16);S('M2_1',-.25,.29,16);S('ATX_24P',1.1,.18,15);S('CPU_8P',-1.0,-1.05,15);
  c.strokeStyle='rgba(235,238,242,.6)';c.lineWidth=2;c.strokeRect(U(-.57),V(.08),U(.07)-U(-.57),V(.22)-V(.08));
  txt(c,'DesmontAR',U(.55),V(1.27),40,'rgba(245,197,24,.9)','center',800);txt(c,'B650 · ATX',U(.55),V(1.34),20,'rgba(235,238,242,.7)','center',700);});
function mkMobo(full){const g=new THREE.Group();
  g.add(at(rbox(2.4,.05,2.8,.008,mat(0x1b1f24,{roughness:.7})),0,.025,0));g.add(decal(2.4,2.8,moboTex,.051,{transparent:false,roughness:.65}));
  const sock=new THREE.Group();sock.userData.id='socket';sock.position.set(-.3,0,-.55);g.add(sock);
  sock.add(at(rbox(.64,.05,.64,.01,mat(0x9aa1ab,{metalness:.8,roughness:.35})),0,.085,0));
  const pins=canvasTex(256,256,(c,w,h)=>{c.fillStyle='#2a2d33';c.fillRect(0,0,w,h);c.fillStyle='#d9ae4f';for(let y=8;y<h;y+=9)for(let x=8;x<w;x+=9)if(!(x>96&&x<160&&y>96&&y<160))c.fillRect(x,y,4,4);},'pins');
  sock.add(decal(.5,.5,pins,.111,{metalness:.8,roughness:.3,transparent:false}));
  const st=new THREE.Mesh(new THREE.ShapeGeometry(new THREE.Shape([new THREE.Vector2(0,0),new THREE.Vector2(.07,0),new THREE.Vector2(0,.07)])),mat(0xe0b44a,{metalness:.8,side:THREE.DoubleSide}));
  st.rotation.x=-PI/2;st.position.set(-.28,.112,.28);sock.add(st);
  const lever=cyl(.012,.62,METAL());lever.rotation.x=PI/2;lever.position.set(.35,.1,0);sock.add(lever);sock.add(at(box(.08,.012,.03,METAL()),.38,.1,.31));
  const vm=mat(0xffffff,{map:finsTex,metalness:.8,roughness:.35});
  g.add(at(rbox(.95,.18,.18,.02,vm),-.3,.14,-1.1));const v2=rbox(.18,.18,.8,.02,vm);v2.position.set(-.95,.14,-.55);g.add(v2);
  for(let i=0;i<8;i++){g.add(at(cyl(.028,.07,mat(0x2b2f36,{metalness:.6,roughness:.4}),null,16),-.72+i*.085,.085,-.88));}
  for(let i=0;i<6;i++){g.add(at(cyl(.028,.07,mat(0x2b2f36,{metalness:.6,roughness:.4}),null,16),-.74,.085,-1.0+i*.13));}
  for(const [k,x] of Object.entries(RAMX)){const s=new THREE.Group();s.userData.id=k;s.position.x=x;g.add(s);
    s.add(at(rbox(.07,.07,1.2,.01,PLASTIC((k==='A2'||k==='B2')?0x59616d:0x16191d)),0,.09,-.55));
    s.add(at(rbox(.085,.1,.05,.01,PLASTIC(0xe9eef5)),0,.1,-1.17));s.add(at(rbox(.085,.1,.05,.01,PLASTIC(0xe9eef5)),0,.1,.07));}
  const x16=new THREE.Group();x16.userData.id='x16';x16.position.set(-.35,0,.5);g.add(x16);x16.add(at(rbox(1.52,.06,.1,.01,BRUSHED()),0,.085,0));x16.add(at(box(1.46,.01,.035,0x0c0e11),0,.116,0));
  const x1=new THREE.Group();x1.userData.id='x1';x1.position.set(-.85,0,.88);g.add(x1);x1.add(at(rbox(.45,.06,.09,.01,PLASTIC(0x16191d)),0,.085,0));x1.add(at(box(.4,.01,.03,0x050607),0,.116,0));
  const m2=new THREE.Group();m2.userData.id='m2';m2.position.set(-.25,0,.15);g.add(m2);m2.add(at(rbox(.06,.04,.16,.006,PLASTIC(0x16191d)),-.3,.07,0));m2.add(at(cyl(.022,.03,METAL()),.3,.065,0));m2.add(at(box(.6,.004,.16,0x232831),0,.052,0));
  g.add(at(rbox(.5,.1,.5,.03,mat(0x2e333b,{metalness:.8,roughness:.3})),.45,.1,.95));
  const lg=canvasTex(256,256,(c,w,h)=>{c.clearRect(0,0,w,h);c.strokeStyle='#f5c518';c.lineWidth=8;c.beginPath();c.moveTo(30,200);c.lineTo(128,40);c.lineTo(226,200);c.stroke();txt(c,'DesmontAR',128,170,30,'#e9eef5','center',800);},'chipset');
  g.add(at(decal(.44,.44,lg,0),.45,.152,.95));
  g.add(at(rbox(.16,.14,.55,.01,PLASTIC(0xece9e2)),1.1,.12,-.2));
  const hp=canvasTex(64,256,(c,w,h)=>{c.fillStyle='#ece9e2';c.fillRect(0,0,w,h);c.fillStyle='#3a3a3a';for(let y=0;y<12;y++)for(let x=0;x<2;x++)rrect(c,8+x*28,6+y*21,20,15,3)||c.fill();},'hdr24');
  g.add(at(decal(.14,.53,hp,0,{transparent:false}),1.1,.191,-.2));
  g.add(at(rbox(.14,.12,.24,.01,PLASTIC(0xece9e2)),-1.0,.11,-1.25));
  g.add(at(rbox(.12,.36,.9,.01,mat(0x6b737e,{metalness:.8,roughness:.4})),-1.14,.2,-.55));
  g.add(at(cyl(.075,.016,METAL()),.75,.06,.45));
  if(full){g.userData.labels={};for(const k of Object.keys(RAMX)){const l=label(k,{size:.13});l.position.set(RAMX[k],.34,-1.33);g.add(l);g.userData.labels[k]=l;}
    const lx=label('PCIe x16',{size:.11});lx.position.set(-.35,.25,.64);g.add(lx);const l1=label('x1',{size:.11});l1.position.set(-.85,.25,1.0);g.add(l1);}
  return g;}


/* ---------- peças de robótica e eletrônica ---------- */
const PIN={GND:[-1.35,-.72],'13':[-1.2,-.72],'12':[-1.05,-.72],'11':[-.9,-.72],'5V':[-1.2,.32]};
const ardTex=canvasTex(1024,768,(c,w,h)=>{c.fillStyle='#0b8a8f';c.fillRect(0,0,w,h);traces(c,w,h,160,'rgba(150,230,230,.22)',11);
  const U=x=>(x+.8)/1.6*w,V=z=>(z+.6)/1.2*h;
  txt(c,'DIGITAL (PWM ~)',U(-.2),V(-.36),22,'#e9fbfb','center',700);
  ['GND','13','12','~11','~10','~9','8','7','~6','~5','4','~3','2','1','0'].forEach((s,i)=>{if(i<4)return;});
  txt(c,'POWER',U(-.3),V(.38),22,'#e9fbfb','center',700);txt(c,'ANALOG IN',U(.4),V(.38),22,'#e9fbfb','center',700);
  txt(c,'UNO',U(-.2),V(.02),96,'#e9fbfb','center',800);c.strokeStyle='#e9fbfb';c.lineWidth=7;c.beginPath();c.ellipse(U(-.3),V(-.18),22,16,0,0,7);c.stroke();c.beginPath();c.ellipse(U(-.24),V(-.18),22,16,0,0,7);c.stroke();
  txt(c,'ARDUINO',U(-.06),V(-.18),30,'#e9fbfb','left',800);
  ['L','TX','RX','ON'].forEach((s,i)=>txt(c,s,U(-.12+i*.07),V(-.26),16,'#e9fbfb','center',700));
  c.strokeStyle='#e9fbfb';c.lineWidth=3;rrect(c,U(.02),V(-.02),U(.69)-U(.02),V(.3)-V(-.02),8);c.stroke();});
function mkArduino(){const g=new THREE.Group();
  g.add(at(rbox(1.6,.04,1.2,.015,mat(0x0b8a8f,{roughness:.55})),0,.02,0));g.add(decal(1.6,1.2,ardTex,.0405,{transparent:false,roughness:.5}));
  const holes=canvasTex(512,64,(c,w,h)=>{c.fillStyle='#14171b';c.fillRect(0,0,w,h);c.fillStyle='#000';for(let x=10;x<w;x+=30)c.fillRect(x,20,16,24);},'hdrHoles');
  const hdr=(L,x,z)=>{g.add(at(rbox(L,.09,.075,.006,PLASTIC(0x14171b)),x,.085,z));g.add(at(decal(L,.07,holes,0,{transparent:false}),x,.131,z));};
  hdr(.9,-.2,-.52);hdr(.55,-.3,.52);hdr(.45,.4,.52);
  const usb=at(rbox(.32,.2,.3,.01,BRUSHED()),-.72,.12,.25);g.add(usb);const uo=face(.2,.12,canvasTex(32,32,(c)=>{c.fillStyle='#0d0f12';c.fillRect(0,0,32,32);},'dark'));uo.rotation.y=-PI/2;uo.position.set(-.881,.12,.25);g.add(uo);
  g.add(at(rbox(.28,.2,.22,.02,PLASTIC(0x111316)),-.72,.12,-.18));
  const chip=at(rbox(.7,.06,.18,.006,PLASTIC(0x16181c,{roughness:.35})),.35,.075,.15);g.add(chip);
  const ct=canvasTex(512,128,(c,w,h)=>{c.clearRect(0,0,w,h);txt(c,'ATMEGA328P',w/2,48,40,'rgba(220,224,230,.75)','center',700);txt(c,'DESMONT · 2026',w/2,92,24,'rgba(220,224,230,.5)','center',600);c.fillStyle='rgba(220,224,230,.4)';c.beginPath();c.arc(30,64,10,0,7);c.fill();},'atmega');
  g.add(at(decal(.68,.16,ct,0),.35,.1055,.15));
  for(let i=0;i<14;i++)for(const s of [-1,1])g.add(at(box(.016,.03,.03,METAL()),.35-.315+i*.0485,.055,.15+s*.1));
  g.add(at(rbox(.14,.05,.06,.02,METAL()),.05,.065,-.25));g.add(at(rbox(.08,.04,.08,.01,METAL()),-.58,.06,-.45));g.add(at(cyl(.025,.03,PLASTIC(0xd23b3b)),-.58,.085,-.45));
  [[-.03,0xffc21a],[.04,0x36d399],[.11,0xffc21a],[.18,0x36d399]].forEach(([x,col])=>g.add(at(box(.03,.015,.02,mat(col,{emissive:col,emissiveIntensity:.5})),x,.048,-.3)));
  return g;}
function mkPins(g,which){const out={};for(const k of which){const [x,z]=PIN[k];const p=at(rbox(.11,.12,.11,.012,PLASTIC(k==='GND'?0x2b2f36:0x16191d)),x,.11,z);p.userData.id=k;g.add(p);
  const hole=at(box(.05,.01,.05,GOLD()),x,.175,z);g.add(hole);
  const l=label(k,{size:.1});l.position.set(x,.33,z+(z<0?-.1:.1));g.add(l);out[k]=new THREE.Vector3(x,.17,z);}return out;}
const protoTex=canvasTex(1024,704,(c,w,h)=>{c.fillStyle='#f3f1eb';c.fillRect(0,0,w,h);
  const hole=(x,y)=>{c.fillStyle='#8b8a86';c.fillRect(x-6,y-6,12,12);c.fillStyle='#2c2c2c';c.fillRect(x-4,y-4,8,8);};
  c.fillStyle='#d23b3b';c.fillRect(30,22,w-60,4);c.fillStyle='#2b62c9';c.fillRect(30,88,w-60,4);c.fillStyle='#d23b3b';c.fillRect(30,h-92,w-60,4);c.fillStyle='#2b62c9';c.fillRect(30,h-26,w-60,4);
  for(let i=0;i<30;i++){const x=56+i*31;if(i%6!==5){hole(x,44);hole(x,68);hole(x,h-70);hole(x,h-46);}
    for(let r=0;r<5;r++){hole(x,138+r*30);hole(x,h-260+r*30+38);}
    if(i%5===0)txt(c,String(i+1),x,118,16,'#6b6a66','center',700);}
  'abcde'.split('').forEach((s,r)=>txt(c,s,30,138+r*30,16,'#6b6a66','center',700));'fghij'.split('').forEach((s,r)=>txt(c,s,30,h-222+r*30,16,'#6b6a66','center',700));
  c.fillStyle='#d9d6ce';c.fillRect(0,h/2-10,w,20);txt(c,'+',14,24,22,'#d23b3b','center',800);txt(c,'−',14,90,22,'#2b62c9','center',800);});
function mkProto(){const g=new THREE.Group();g.add(at(rbox(1.5,.08,1.03,.015,PLASTIC(0xf3f1eb,{roughness:.7})),0,.04,0));g.add(decal(1.5,1.03,protoTex,.0805,{transparent:false,roughness:.7}));return g;}
const ledProfile=(()=>{const p=[new THREE.Vector2(0,.055),new THREE.Vector2(.086,.055),new THREE.Vector2(.086,.08),new THREE.Vector2(.071,.08),new THREE.Vector2(.071,.2)];for(let a=1;a<=10;a++){const t=a/10*PI/2;p.push(new THREE.Vector2(.071*Math.cos(t),.2+.071*Math.sin(t)));}return p;})();
function mkLED(color,on=false){const g=new THREE.Group();const c=new THREE.Color(color);
  const lens=mat(color,{transparent:true,opacity:.78,roughness:.12,metalness:0,emissive:c.clone().multiplyScalar(.06)});
  g.add(new THREE.Mesh(new THREE.LatheGeometry(ledProfile,28),lens));
  g.add(at(box(.03,.05,.012,METAL({roughness:.4})),-.018,.13,0));g.add(at(box(.02,.04,.012,METAL({roughness:.4})),.02,.12,0));
  const lm=METAL({roughness:.35});g.add(wire([[-.025,.06,0],[-.025,.0,0]],0xc9cdd3,.008));g.add(wire([[.025,.06,0],[.025,.02,0],[.05,.0,0]],0xc9cdd3,.008));
  const h=halo(color,.65);h.position.y=.19;h.visible=false;g.add(h);
  g.userData.set=v=>{const k=typeof v==='number'?v:(v?1:0);lens.emissive.copy(c).multiplyScalar(.06+k*1.15);h.visible=k>0.02;h.material.opacity=Math.min(1,k);h.scale.setScalar(.35+.4*k);};g.userData.set(on);g.userData.color=color;return g;}
const BANDC={black:0x111111,brown:0x7a4a24,red:0xd23b3b,orange:0xf08a24,yellow:0xf5c518,green:0x2fa65a,blue:0x2b62c9,violet:0x8a4fd1,gray:0x8b8f97,white:0xf2f2f2,gold:0xd9ae4f};
const resProfile=[[0,-.15],[.035,-.15],[.045,-.13],[.046,-.09],[.036,-.07],[.036,.07],[.046,.09],[.045,.13],[.035,.15],[0,.15]].map(([r,y])=>new THREE.Vector2(r,y));
function mkResistor(bands=['red','red','brown']){const g=new THREE.Group();const b=new THREE.Group();b.rotation.z=PI/2;b.position.y=.1;g.add(b);
  b.add(new THREE.Mesh(new THREE.LatheGeometry(resProfile,24),mat(0xd9c49a,{roughness:.45})));
  [[-.11,.047,bands[0]],[-.04,.0375,bands[1]],[0,.0375,bands[2]],[.11,.047,'gold']].forEach(([y,r,col])=>{const bb=cyl(r,.022,mat(BANDC[col],{roughness:.4,metalness:col==='gold'?.7:0}),null,24);bb.position.y=y;b.add(bb);});
  for(const s of [-1,1])g.add(wire([[s*.15,.1,0],[s*.26,.1,0],[s*.3,.06,0],[s*.3,0,0]],0xc9cdd3,.008));return g;}
function mkUSB(){const g=new THREE.Group();g.add(at(rbox(.32,.16,.22,.02,PLASTIC(0x2b2f36)),0,.08,0));g.add(at(box(.16,.12,.17,BRUSHED()),-.22,.08,0));
  g.add(wire([[.16,.08,0],[.45,.06,.05],[.7,.05,-.15],[.95,.05,0]],0x2b2f36,.035));return g;}
function mkJumper(color,pts){const g=new THREE.Group();g.add(wire(pts,color,.02));const a=pts[0],b=pts[pts.length-1];
  for(const p of [a,b]){g.add(at(rbox(.05,.09,.05,.006,PLASTIC(0x16191d)),p[0],p[1]+.045,p[2]));}return g;}

/* eletrônica básica */
function mkBattery(){const g=new THREE.Group();g.add(at(rbox(.45,.8,.26,.03,PLASTIC(0x1a1d22,{roughness:.4})),0,.4,0));
  const t=canvasTex(512,880,(c,w,h)=>{const gr=c.createLinearGradient(0,0,0,h);gr.addColorStop(0,'#1b1e23');gr.addColorStop(1,'#2b3038');c.fillStyle=gr;c.fillRect(0,0,w,h);c.fillStyle='#d9ae4f';c.fillRect(0,h*.55,w,h*.45);
    txt(c,'9V',w/2,h*.3,200,'#d9ae4f','center',800);txt(c,'DESMONT',w/2,h*.48,48,'#e9eef5','center',800);txt(c,'ALCALINA',w/2,h*.7,48,'#14181e','center',800);txt(c,'+  −',w/2,h*.85,64,'#14181e','center',800);},'bat9v');
  const f=face(.43,.78,t,{roughness:.35});f.position.set(0,.4,.131);g.add(f);
  const p=at(cyl(.05,.06,METAL(),null,20),-.1,.83,0);g.add(p);const n=at(cyl(.065,.06,METAL(),null,6),.1,.83,0);g.add(n);
  g.add(at(label('+',{size:.12,bg:'#d23b3b'}),-.1,1.0,0));g.add(at(label('−',{size:.12,bg:'#2b62c9'}),.1,1.0,0));
  g.userData.plus=new THREE.Vector3(-.1,.86,0);g.userData.minus=new THREE.Vector3(.1,.86,0);return g;}
function mkBulb(){const g=new THREE.Group();g.add(at(rbox(.34,.08,.3,.02,PLASTIC(0xece9e2)),0,.04,0));
  for(const x of [-.12,.12])g.add(at(cyl(.03,.04,METAL()),x,.1,0));
  const th=canvasTex(64,64,(c,w,h)=>{for(let y=0;y<h;y+=8){const gr=c.createLinearGradient(0,y,0,y+8);gr.addColorStop(0,'#8b8f97');gr.addColorStop(.5,'#eef0f3');gr.addColorStop(1,'#7a7f88');c.fillStyle=gr;c.fillRect(0,y,w,8);}},'thread');
  th.wrapS=th.wrapT=THREE.RepeatWrapping;g.add(at(cyl(.065,.13,mat(0xffffff,{map:th,metalness:.9,roughness:.3})),0,.145,0));
  const glass=new THREE.Mesh(new THREE.SphereGeometry(.14,32,20),mat(0xf3f6fa,{transparent:true,opacity:.38,roughness:.04,metalness:.1,depthWrite:false}));glass.position.y=.34;g.add(glass);
  const fm=mat(0x553311,{emissive:0xff9a3d,emissiveIntensity:0});g.add(wire([[-.03,.2,0],[-.03,.34,0]],0x888888,.004));g.add(wire([[.03,.2,0],[.03,.34,0]],0x888888,.004));
  const fil=new THREE.Mesh(new THREE.TubeGeometry(new THREE.CatmullRomCurve3([[-.03,.34,0],[-.015,.36,0],[0,.34,0],[.015,.36,0],[.03,.34,0]].map(p=>new THREE.Vector3(...p))),24,.005,6),fm);g.add(fil);
  const h=halo(0xffc46b,1.1);h.position.y=.34;h.visible=false;g.add(h);
  g.userData.set=v=>{fm.emissiveIntensity=v*3;h.visible=v>.02;h.material.opacity=Math.min(1,v);h.scale.setScalar(.4+.9*v);glass.material.emissive=new THREE.Color(0xffc46b).multiplyScalar(v*.5);};
  g.userData.a=new THREE.Vector3(-.12,.12,0);g.userData.b=new THREE.Vector3(.12,.12,0);return g;}
function mkSwitch(){const g=new THREE.Group();g.add(at(rbox(.3,.1,.2,.02,PLASTIC(0x16191d)),0,.05,0));g.add(at(cyl(.045,.04,METAL()),0,.12,0));
  const lv=new THREE.Group();lv.position.y=.13;g.add(lv);lv.add(at(cyl(.016,.2,METAL()),0,.1,0));lv.add(at(new THREE.Mesh(new THREE.SphereGeometry(.024,16,10),METAL()),0,.2,0));
  for(const x of [-.11,.11])g.add(at(cyl(.022,.03,METAL()),x,.115,0));
  g.userData.set=on=>{lv.rotation.z=on?-.5:.5;};g.userData.set(true);g.userData.a=new THREE.Vector3(-.11,.12,0);g.userData.b=new THREE.Vector3(.11,.12,0);return g;}
function mkCap(){const g=new THREE.Group();const t=canvasTex(256,128,(c,w,h)=>{c.fillStyle='#1f2a6b';c.fillRect(0,0,w,h);c.fillStyle='#c9cfe0';c.fillRect(0,0,52,h);for(let y=10;y<h;y+=30)txt(c,'−',26,y+8,30,'#1f2a6b','center',800);txt(c,'470µF',150,50,24,'#c9cfe0','center',700);txt(c,'16V',150,86,22,'#c9cfe0','center',700);},'cap');
  const b=cyl(.08,.22,mat(0xffffff,{map:t,roughness:.35}));b.position.y=.17;g.add(b);
  const top=at(cyl(.075,.004,METAL()),0,.282,0);g.add(top);
  g.add(wire([[-.03,.06,0],[-.03,0,0]],0xc9cdd3,.008));g.add(wire([[.03,.06,0],[.03,0,0]],0xc9cdd3,.008));return g;}
function mkTransistor(){const g=new THREE.Group();const body=new THREE.Mesh(new THREE.CylinderGeometry(.075,.075,.17,24,1,false,0,PI),PLASTIC(0x16181c,{roughness:.4,side:THREE.DoubleSide}));body.position.y=.24;g.add(body);
  const t=canvasTex(256,256,(c,w,h)=>{c.fillStyle='#16181c';c.fillRect(0,0,w,h);txt(c,'BC548',w/2,100,52,'#cfd4dc','center',700);txt(c,'NPN',w/2,160,40,'#9aa3af','center',700);},'tr');
  const f=face(.15,.17,t,{transparent:false});f.position.set(0,.24,0);f.rotation.y=PI;g.add(f);
  g.userData.legs={};['E','B','C'].forEach((k,i)=>{const lg=new THREE.Group();lg.add(at(box(.02,.16,.02,METAL()),(i-1)*.045,.08,0));lg.add(at(box(.07,.12,.07,mat(0,{transparent:true,opacity:0})),(i-1)*.045,.08,0));lg.userData.leg=k;g.add(lg);g.userData.legs[k]=lg;
    const l=label(k,{size:.08});l.position.set((i-1)*.07,.05,-.12);g.add(l);});return g;}
function mkMotor(){const g=new THREE.Group();const b=cyl(.14,.3,BRUSHED());b.rotation.z=PI/2;b.position.set(0,.14,0);g.add(b);
  const cap=cyl(.142,.05,PLASTIC(0x16191d));cap.rotation.z=PI/2;cap.position.set(-.17,.14,0);g.add(cap);
  const sh=cyl(.012,.12,METAL());sh.rotation.z=PI/2;sh.position.set(.21,.14,0);g.add(sh);
  const prop=new THREE.Group();prop.position.set(.27,.14,0);g.add(prop);for(let i=0;i<3;i++){const bl=box(.012,.26,.05,PLASTIC(0xf5c518));bl.geometry.translate(0,.13,0);const p=new THREE.Group();bl.rotation.y=.4;p.add(bl);p.rotation.x=i*2*PI/3;prop.add(p);}
  prop.add(at(new THREE.Mesh(new THREE.SphereGeometry(.035,16,10),PLASTIC(0xf5c518)),0,0,0));g.userData.prop=prop;return g;}
function mkPot(){const g=new THREE.Group();g.add(at(rbox(.24,.12,.24,.015,PLASTIC(0x1d4fa0)),0,.06,0));g.add(at(cyl(.05,.05,METAL()),0,.145,0));
  const knob=new THREE.Group();knob.position.y=.2;g.add(knob);const kt=canvasTex(64,64,(c,w,h)=>{c.fillStyle='#1a1d22';c.fillRect(0,0,w,h);c.fillStyle='#2e333b';for(let x=0;x<w;x+=6)c.fillRect(x,0,3,h);},'knurl');kt.wrapS=THREE.RepeatWrapping;kt.repeat.set(6,1);
  knob.add(cyl(.085,.09,mat(0xffffff,{map:kt,roughness:.5})));knob.add(at(box(.012,.005,.07,mat(0xffffff,{emissive:0xffffff,emissiveIntensity:.3})),0,.046,-.03));
  for(const x of [-.07,0,.07])g.add(wire([[x,.02,.1],[x,.0,.14]],0xc9cdd3,.008));g.userData.knob=knob;return g;}
function mkButton(color=0xd23b3b){const g=new THREE.Group();g.add(at(rbox(.22,.07,.22,.012,PLASTIC(0x16191d)),0,.035,0));g.add(at(box(.2,.005,.2,METAL()),0,.073,0));
  const cap=at(cyl(.06,.05,PLASTIC(color,{roughness:.35})),0,.1,0);g.add(cap);g.userData.cap=cap;return g;}
function mkMultimeter(){const g=new THREE.Group();g.add(at(rbox(.72,.12,1.12,.06,PLASTIC(0xf5c518,{roughness:.5})),0,.06,0));
  g.add(at(rbox(.6,.03,1.0,.02,PLASTIC(0x23272e)),0,.12,0));
  const lc=document.createElement('canvas');lc.width=384;lc.height=160;const lt=new THREE.CanvasTexture(lc);lt.encoding=THREE.sRGBEncoding;
  const lcd=decal(.5,.2,lt,.137,{transparent:false,emissive:0x1a2a10,roughness:.3});lcd.position.z=-.32;g.add(lcd);
  g.userData.setLCD=s=>{const c=lc.getContext('2d');c.fillStyle='#b8c79a';c.fillRect(0,0,384,160);txt(c,s,360,84,92,'#1c2414','right',700,'"Courier New", monospace');lt.needsUpdate=true;};g.userData.setLCD('0.00');
  const dial=new THREE.Group();dial.position.set(0,.135,.12);g.add(dial);dial.add(cyl(.16,.04,PLASTIC(0x111316)));dial.add(at(box(.03,.01,.15,mat(0xffffff,{emissive:0xffffff,emissiveIntensity:.2})),0,.022,-.07));
  const pos={off:-90,dcv:-35,acv:10,ohm:55,cont:125,a:180};const names={off:'OFF',dcv:'V⎓',acv:'V~',ohm:'Ω',cont:'♪',a:'A'};g.userData.spots={};
  for(const [k,a] of Object.entries(pos)){const r=a*PI/180;const x=Math.cos(r)*.24,z=Math.sin(r)*.24;const s=at(cyl(.04,.014,PLASTIC(0x3a3f47)),x,.142,.12+z);s.userData.spot=k;g.add(s);g.userData.spots[k]=s;
    const l=label(names[k],{size:.075,bg:'rgba(20,26,34,.85)'});l.position.set(x*1.25,.2,.12+z*1.25);g.add(l);}
  g.userData.setDial=k=>{dial.rotation.y=-(pos[k]+90)*PI/180;};g.userData.setDial('off');
  [[-.18,0x16191d],[0,0xd23b3b],[.18,0xd23b3b]].forEach(([x,c])=>g.add(at(cyl(.035,.03,PLASTIC(c)),x,.14,.46)));
  g.userData.jR=new THREE.Vector3(0,.15,.46);g.userData.jB=new THREE.Vector3(-.18,.15,.46);return g;}
function probe(color,a,b){const g=new THREE.Group();g.add(arcWire(a,[b[0],b[1],b[2]],color,.25,.016));const tip=new THREE.Group();tip.position.set(b[0],b[1],b[2]);g.add(tip);
  const h=cyl(.03,.2,PLASTIC(color));h.rotation.x=PI/2;h.position.z=.1;tip.add(h);const n=cyl(.008,.1,METAL());n.rotation.x=PI/2;n.position.z=.25;tip.add(n);return g;}


/* ---------- peças de redes ---------- */
function ledDots(c,list,y){list.forEach(([x,col,lab])=>{const gr=c.createRadialGradient(x,y,0,x,y,10);gr.addColorStop(0,col);gr.addColorStop(1,'rgba(0,0,0,0)');c.fillStyle=gr;c.beginPath();c.arc(x,y,10,0,7);c.fill();if(lab)txt(c,lab,x,y+24,14,'rgba(220,224,230,.75)','center',700);});}
function mkModem(){const g=new THREE.Group();g.add(at(rbox(.24,.62,.48,.05,PLASTIC(0xf1f1ee,{roughness:.4})),0,.31,0));
  const t=canvasTex(256,640,(c,w,h)=>{c.fillStyle='#f1f1ee';c.fillRect(0,0,w,h);txt(c,'MODEM',w/2,80,40,'#4b5563','center',800);txt(c,'fibra',w/2,124,24,'#9aa3af','center',700);
    c.fillStyle='#e2e2de';for(let y=420;y<600;y+=16)c.fillRect(40,y,w-80,6);
    [['POWER',220],['PON',280],['INTERNET',340]].forEach(([l,y])=>{const gr=c.createRadialGradient(60,y,0,60,y,12);gr.addColorStop(0,'#36d399');gr.addColorStop(1,'rgba(54,211,153,0)');c.fillStyle=gr;c.beginPath();c.arc(60,y,12,0,7);c.fill();txt(c,l,90,y,22,'#4b5563','left',700);});},'modem');
  const f=face(.46,.6,t,{emissive:0x0b2a1c,emissiveIntensity:.2});f.rotation.y=PI/2;f.position.set(.121,.31,0);g.add(f);
  g.userData.port=new THREE.Vector3(-.12,.12,0);return g;}
function mkRouter(){const g=new THREE.Group();g.add(at(rbox(.78,.11,.48,.04,PLASTIC(0x14171b,{roughness:.35})),0,.06,0));
  const t=canvasTex(512,320,(c,w,h)=>{c.fillStyle='#14171b';c.fillRect(0,0,w,h);c.fillStyle='#1e2228';for(let i=0;i<14;i++)rrect(c,40+i*31,40,14,150,7)||c.fill();txt(c,'ROTEADOR Wi-Fi 6',w/2,250,34,'#9aa3af','center',800);},'routerTop');
  g.add(decal(.74,.44,t,.1155,{transparent:false,roughness:.35}));
  const ft=canvasTex(512,64,(c,w,h)=>{c.fillStyle='#14171b';c.fillRect(0,0,w,h);ledDots(c,[[80,'#36d399'],[150,'#36d399'],[220,'#4aa8ff'],[290,'#4aa8ff'],[360,'#36d399'],[430,'#36d399']],30);},'routerFront');
  const ff=face(.76,.09,ft,{emissive:0x0d2a22,emissiveIntensity:.6});ff.position.set(0,.06,.241);g.add(ff);
  for(const [x,rz] of [[-.32,.15],[0,0],[.32,-.15]]){const a=new THREE.Group();a.position.set(x,.1,-.2);a.rotation.z=rz;a.rotation.x=-.12;g.add(a);a.add(at(cyl(.022,.5,PLASTIC(0x14171b)),0,.25,0));a.add(at(new THREE.Mesh(new THREE.SphereGeometry(.022,12,8),PLASTIC(0x14171b)),0,.5,0));a.add(at(cyl(.03,.05,PLASTIC(0x22262c)),0,0,0));}
  g.userData.port=new THREE.Vector3(0,.08,-.24);return g;}
function mkNetSwitch(){const g=new THREE.Group();g.add(at(rbox(1.0,.09,.36,.015,mat(0x8a9099,{metalness:.75,roughness:.35})),0,.045,0));
  const t=canvasTex(1024,96,(c,w,h)=>{c.fillStyle='#7c838c';c.fillRect(0,0,w,h);for(let i=0;i<8;i++){const x=160+i*100;c.fillStyle='#14171b';c.fillRect(x,22,64,50);c.fillStyle='#2b2f36';c.fillRect(x+16,62,32,10);ledDots(c,[[x+10,'#36d399'],[x+54,'#f5c518']],14);}
    txt(c,'SWITCH',70,40,26,'#14181e','center',800);txt(c,'8 PORTAS',70,70,18,'#14181e','center',700);},'switch');
  const f=face(.98,.085,t,{emissive:0x0b1a12,emissiveIntensity:.3});f.position.set(0,.045,.181);g.add(f);g.userData.port=new THREE.Vector3(0,.05,.18);return g;}
const screenTex=canvasTex(512,320,(c,w,h)=>{const gr=c.createLinearGradient(0,0,w,h);gr.addColorStop(0,'#2b62c9');gr.addColorStop(1,'#7c4ad9');c.fillStyle=gr;c.fillRect(0,0,w,h);
  c.fillStyle='rgba(255,255,255,.85)';for(let i=0;i<4;i++)rrect(c,22,24+i*62,46,46,8)||c.fill();c.fillStyle='rgba(20,26,34,.85)';c.fillRect(0,h-34,w,34);txt(c,'DesmontAR',w-20,h-17,20,'#e9eef5','right',700);},'screen');
function mkPC(){const g=new THREE.Group();g.add(at(rbox(.24,.56,.5,.02,mat(0x16191d,{metalness:.4,roughness:.4})),-.42,.28,0));
  const ft=canvasTex(128,256,(c,w,h)=>{c.fillStyle='#16191d';c.fillRect(0,0,w,h);c.strokeStyle='#4aa8ff';c.lineWidth=5;c.beginPath();c.arc(64,46,16,0,7);c.stroke();c.fillStyle='#22262c';for(let y=100;y<240;y+=14)c.fillRect(20,y,88,6);},'pcFront');
  const f=face(.23,.54,ft,{emissive:0x0a1f3a,emissiveIntensity:.4});f.position.set(-.42,.28,.251);g.add(f);
  g.add(at(rbox(.22,.02,.16,.01,PLASTIC(0x22262c)),.12,.01,0));g.add(at(box(.04,.22,.04,PLASTIC(0x22262c)),.12,.12,-.02));
  g.add(at(rbox(.66,.42,.035,.015,PLASTIC(0x111316)),.12,.42,0));const s=face(.62,.38,screenTex,{emissive:0xffffff,emissiveMap:screenTex,emissiveIntensity:.7,transparent:false});s.position.set(.12,.42,.0185);g.add(s);
  g.add(at(rbox(.5,.025,.16,.01,PLASTIC(0x2b2f36)),.12,.013,.28));g.userData.port=new THREE.Vector3(-.42,.15,-.25);return g;}
function mkNotebook(){const g=new THREE.Group();g.add(at(rbox(.62,.03,.42,.015,mat(0xb9bec6,{metalness:.8,roughness:.35})),0,.015,0));
  const kt=canvasTex(512,256,(c,w,h)=>{c.fillStyle='#b9bec6';c.fillRect(0,0,w,h);c.fillStyle='#2b2f36';for(let r=0;r<5;r++)for(let k=0;k<14;k++)rrect(c,24+k*33,20+r*30,27,24,3)||c.fill();c.fillStyle='#a7adb6';rrect(c,170,180,170,62,8);c.fill();},'kbd');
  g.add(at(decal(.6,.4,kt,0,{transparent:false,roughness:.5}),0,.0305,0));
  const lid=new THREE.Group();lid.position.set(0,.03,-.2);lid.rotation.x=-1.85+PI/2;g.add(lid);lid.add(at(rbox(.62,.4,.02,.015,mat(0xb9bec6,{metalness:.8,roughness:.35})),0,.2,0));
  const s=face(.57,.35,screenTex,{emissive:0xffffff,emissiveMap:screenTex,emissiveIntensity:.7,transparent:false});s.position.set(0,.2,.0105);lid.add(s);return g;}
function mkPhone(){const g=new THREE.Group();const p=new THREE.Group();p.rotation.x=-1.0;p.position.y=.16;g.add(p);
  p.add(rbox(.16,.32,.016,.025,PLASTIC(0x111316,{roughness:.3})));const s=face(.145,.3,canvasTex(128,256,(c,w,h)=>{const gr=c.createLinearGradient(0,0,0,h);gr.addColorStop(0,'#36d399');gr.addColorStop(1,'#2b62c9');c.fillStyle=gr;c.fillRect(0,0,w,h);c.fillStyle='rgba(255,255,255,.85)';for(let i=0;i<3;i++)for(let k=0;k<3;k++)rrect(c,14+k*38,40+i*42,28,28,7)||c.fill();},'phone'),{emissive:0xffffff,emissiveIntensity:.5,transparent:false});
  s.material.emissiveMap=s.material.map;s.position.z=.0085;p.add(s);g.add(at(rbox(.14,.12,.08,.01,PLASTIC(0x2b2f36)),0,.06,.05));return g;}
function mkServer(){const g=new THREE.Group();g.add(at(rbox(.4,.9,.5,.02,mat(0x1a1d22,{metalness:.5,roughness:.4})),0,.45,0));
  const t=canvasTex(256,576,(c,w,h)=>{c.fillStyle='#1a1d22';c.fillRect(0,0,w,h);for(let i=0;i<8;i++){c.fillStyle='#2b2f36';rrect(c,20,30+i*64,w-40,50,6);c.fill();ledDots(c,[[w-46,i%3?'#36d399':'#4aa8ff']],55+i*64);c.fillStyle='#14171b';for(let k=0;k<6;k++)c.fillRect(36+k*16,42+i*64,8,26);}txt(c,'SERVIDOR',w/2,h-18,22,'#9aa3af','center',800);},'server');
  const f=face(.38,.88,t,{emissive:0x0b2a1c,emissiveIntensity:.5});f.position.set(0,.45,.251);g.add(f);g.userData.port=new THREE.Vector3(0,.2,-.25);return g;}
function mkCloud(){const g=new THREE.Group();const m=mat(0xeef3ff,{roughness:.9,emissive:0x9fb4d8,emissiveIntensity:.15});
  [[0,0,0,.32],[.3,-.05,.05,.25],[-.3,-.06,.02,.24],[.12,.12,-.05,.26],[-.14,.1,.04,.22]].forEach(([x,y,z,r])=>g.add(at(new THREE.Mesh(new THREE.SphereGeometry(r,24,16),m),x,y,z)));
  const l=label('Internet',{size:.16});l.position.set(0,.45,0);g.add(l);return g;}
/* cabo de rede com conectores nas pontas */
function netCable(a,b,color=0x2b62c9,h=.3){const g=new THREE.Group();const w=arcWire(a,b,color,h,.022);g.add(w);g.userData.curve=w.userData.curve;
  for(const p of [a,b]){g.add(at(rbox(.06,.05,.09,.01,mat(0xffffff,{transparent:true,opacity:.6,roughness:.15})),p[0],p[1]+.02,p[2]));}return g;}
/* pacotes de dados andando no cabo */
function addFlow(curve,color=0x4aa8ff,n=3,speed=.45,back){const grp=new THREE.Group();bench.add(grp);const ps=[];
  for(let i=0;i<n;i++){const s=new THREE.Mesh(new THREE.SphereGeometry(.04,14,10),mat(color,{emissive:color,emissiveIntensity:1.4}));const h=halo(color,.16);s.add(h);grp.add(s);ps.push(s);}
  const f={grp,t:0,on:true};R.updaters.push(dt=>{if(!f.on){grp.visible=false;return;}grp.visible=true;f.t+=dt*speed;ps.forEach((s,i)=>{let u=(f.t+i/n)%1;if(back)u=1-u;s.position.copy(curve.getPointAt(u));});});return f;}
function wifiRings(pos,color=0x4aa8ff){const grp=new THREE.Group();grp.position.copy(pos);bench.add(grp);const rings=[];
  for(let i=0;i<3;i++){const r=new THREE.Mesh(new THREE.TorusGeometry(1,.012,6,64),new THREE.MeshBasicMaterial({color,transparent:true,opacity:.6,toneMapped:false}));r.rotation.x=PI/2;grp.add(r);rings.push(r);}
  const f={grp,t:0,on:true};R.updaters.push(dt=>{grp.visible=f.on;f.t+=dt*.5;rings.forEach((r,i)=>{const u=(f.t+i/3)%1;r.scale.setScalar(.1+u*1.1);r.material.opacity=.7*(1-u);});});return f;}
const T568B=[['w1','branco-laranja',0xf08a24,1],['w2','laranja',0xf08a24,0],['w3','branco-verde',0x2fa65a,1],['w4','azul',0x2b62c9,0],['w5','branco-azul',0x2b62c9,1],['w6','verde',0x2fa65a,0],['w7','branco-marrom',0x7a4a24,1],['w8','marrom',0x7a4a24,0]];
function stripeTex(col){return canvasTex(64,64,(c,w,h)=>{c.fillStyle='#f2f2f2';c.fillRect(0,0,w,h);c.fillStyle='#'+col.toString(16).padStart(6,'0');for(let x=-h;x<w;x+=22){c.beginPath();c.moveTo(x,0);c.lineTo(x+10,0);c.lineTo(x+10+h,h);c.lineTo(x+h,h);c.fill();}},'st'+col);}
function mkRJ45(){const g=new THREE.Group();
  const body=rbox(1.0,.32,.9,.03,mat(0xffffff,{transparent:true,opacity:.28,roughness:.08,metalness:0,depthWrite:false}));body.position.set(0,.2,-.2);body.userData.noPick=1;g.add(body);
  const clip=at(rbox(.42,.04,.6,.02,mat(0xffffff,{transparent:true,opacity:.4,roughness:.1,depthWrite:false})),0,.38,0);clip.userData.noPick=1;g.add(clip);
  const sheath=cyl(.13,.5,PLASTIC(0x2b62c9));sheath.rotation.x=PI/2;sheath.position.set(0,.2,1.1);g.add(sheath);
  g.userData.wires={};T568B.forEach(([id,nm,col,str],i)=>{const x=-.385+i*.11;const t=str?stripeTex(col):null;if(t){t.wrapS=t.wrapT=THREE.RepeatWrapping;t.repeat.set(8,1);}
    const w=wire([[x,.22,-.55],[x,.22,-.1],[x*.6,.2,.3],[x*.35,.2,.7]],str?0xffffff:col,.035,t);const grp=new THREE.Group();grp.add(w);grp.userData.wire=id;g.add(grp);g.userData.wires[id]=grp;
    g.add(at(box(.06,.03,.25,GOLD()),x,.35,-.5));const l=label(String(i+1),{size:.09});l.position.set(x,.5,-.62);g.add(l);});
  return g;}
/* casa vista de cima (Wi-Fi) */
function mkHouse(){const g=new THREE.Group();const fl=canvasTex(512,512,(c,w,h)=>{c.fillStyle='#d8c6a8';c.fillRect(0,0,w,h);c.strokeStyle='rgba(120,90,60,.25)';for(let y=0;y<h;y+=32){c.beginPath();c.moveTo(0,y);c.lineTo(w,y);c.stroke();}},'floor');
  g.add(at(rbox(3.3,.04,3.3,.01,mat(0xffffff,{map:fl,roughness:.8})),0,.02,0));const wm=PLASTIC(0xf3f1ec,{roughness:.8});const W=(w,d,x,z)=>g.add(at(box(w,.32,d,wm),x,.2,z));
  W(3.3,.06,0,-1.62);W(3.3,.06,0,1.62);W(.06,3.3,-1.62,0);W(.06,3.3,1.62,0);W(1.2,.06,-1.0,0);W(.8,.06,1.2,0);W(.06,1.2,0,-1.0);W(.06,.9,0,1.15);
  const lab=(s,x,z)=>{const l=label(s,{size:.12,bg:'rgba(20,26,34,.75)'});l.position.set(x,.5,z);g.add(l);};lab('Quarto',-.8,-.8);lab('Cozinha',.8,-.8);lab('Sala',-.6,.8);lab('Banheiro',1.0,.9);
  g.add(at(rbox(.6,.12,.36,.02,PLASTIC(0x5a6b82)),-.9,.08,1.2));g.add(at(rbox(.6,.08,.8,.02,PLASTIC(0x9a7ad1)),-1.1,.06,-1.05));
  g.add(at(rbox(.36,.22,.26,.02,mat(0xdfe3e8,{metalness:.5,roughness:.3})),1.2,.13,-1.38));const mw=face(.2,.14,canvasTex(64,32,(c)=>{c.fillStyle='#111';c.fillRect(0,0,64,32);},'mwDoor'));mw.position.set(1.15,.13,-1.249);g.add(mw);
  lab('micro-ondas',1.2,-1.05);return g;}
function spot(id,x,z,col=0xf5c518){const g=new THREE.Group();g.position.set(x,.05,z);g.userData.id=id;const d=cyl(.16,.02,mat(col,{emissive:col,emissiveIntensity:.5,transparent:true,opacity:.85}));g.add(d);
  const r=new THREE.Mesh(new THREE.TorusGeometry(.2,.015,6,40),mat(col,{emissive:col,emissiveIntensity:.8}));r.rotation.x=PI/2;g.add(r);return g;}
/* escola: dois laboratórios, secretaria e corredor */
function mkSchool(){const g=new THREE.Group();g.add(at(rbox(3.4,.04,3.2,.01,PLASTIC(0xcfd6de,{roughness:.85})),0,.02,0));const wm=PLASTIC(0xf3f1ec,{roughness:.8});const W=(w,d,x,z)=>g.add(at(box(w,.28,d,wm),x,.18,z));
  W(3.4,.05,0,-1.58);W(3.4,.05,0,1.58);W(.05,3.2,-1.68,0);W(.05,3.2,1.68,0);W(3.4,.05,0,-.35);W(3.4,.05,0,.35);W(.05,1.2,-.4,-.97);W(.05,1.2,.6,.97);
  const lab=(s,x,z)=>{const l=label(s,{size:.12,bg:'rgba(20,26,34,.75)'});l.position.set(x,.48,z);g.add(l);};lab('Laboratório 1',-1.05,-.95);lab('Laboratório 2',.65,-.95);lab('Corredor',0,0);lab('Secretaria',-.55,.95);lab('Biblioteca',1.15,.95);
  const pc=(x,z)=>{g.add(at(rbox(.16,.1,.02,.005,PLASTIC(0x111316)),x,.14,z));g.add(at(box(.18,.06,.1,PLASTIC(0x8a6a4a)),x,.07,z+.05));};
  for(let r=0;r<2;r++)for(let k=0;k<4;k++){pc(-1.5+k*.28,-1.3+r*.4);pc(.15+k*.28,-1.3+r*.4);}
  pc(-1.3,.9);pc(-1.0,.9);return g;}

/* ---------- guias ---------- */
const MEMBERS={ar:['Ana Roberta','#f5c518'],al:['Ana Luísa','#ff8ab3'],lu:['Luiza','#5ee0a8'],gi:['Giovanna','#7fb8ff']};
function av(id){const m=MEMBERS[id];const ini=m[0].split(' ').map(s=>s[0]).join('').slice(0,2);return `<div class="av" style="background:${m[1]}" aria-hidden="true">${ini}</div>`;}
function say(id,text,tag){const m=MEMBERS[id];return `<div class="say">${av(id)}<div><small>${m[0]}${tag?' · '+tag:''}</small><p>${text}</p></div></div>`;}

/* ---------- trilhas ---------- */
const ICON={hw:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><rect x="6" y="6" width="12" height="12" rx="1.5"/><rect x="9.5" y="9.5" width="5" height="5"/><path d="M9 2v3M15 2v3M9 19v3M15 19v3M2 9h3M2 15h3M19 9h3M19 15h3"/></svg>',
  rb:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><rect x="5" y="8" width="14" height="11" rx="3"/><circle cx="9.5" cy="13.5" r="1.4" fill="currentColor"/><circle cx="14.5" cy="13.5" r="1.4" fill="currentColor"/><path d="M12 8V4M10 4h4M3 12v3M21 12v3"/></svg>',
  el:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M13 2L5 14h6l-1 8 8-12h-6z"/></svg>',
  rd:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><rect x="9" y="2" width="6" height="5" rx="1"/><rect x="2" y="17" width="6" height="5" rx="1"/><rect x="16" y="17" width="6" height="5" rx="1"/><path d="M12 7v5M5 17v-5h14v5"/></svg>'};
const TRACKS=[
  {id:'hw',short:'Hardware',name:'Montagem de hardware',desc:'Do primeiro encaixe ao PC completo',c:'#f5c518',ready:3,
   ph:['Conhecendo as peças','O processador','Memória RAM','Armazenamento','Placa de vídeo','Energia','Montagem completa','O PC não liga','Upgrade','Desafio final']},
  {id:'rb',short:'Robótica',name:'Robótica com Arduino',desc:'Do LED piscando ao carrinho autônomo',c:'#4aa8ff',ready:3,
   ph:['Conhecendo o Arduino','Pisca LED','Semáforo','Botão','Buzzer','Sensor de luz','Sensor de distância','Servo motor','O circuito não funciona','Carrinho autônomo']},
  {id:'el',short:'Eletrônica',name:'Eletrônica básica',desc:'Corrente, resistores e circuitos',c:'#ff8a3d',ready:10,
   ph:['O circuito fechado','Protoboard','Resistor','Série e paralelo','Lei de Ohm','Multímetro','Capacitor','Transistor','Achar o curto','Lanterna']},
  {id:'rd',short:'Redes',name:'Redes',desc:'Da rede de casa à rede da escola',c:'#b98cff',ready:10,
   ph:['As peças da rede','O cabo de rede','Rede de casa','Endereço IP','Wi-Fi','Switch','Caminho do dado','Sem internet','Rede segura','Rede da escola']}];
const ROMAN=['I','II','III','IV','V','VI','VII','VIII','IX','X'];

/* ---------- progresso salvo ---------- */
const KEY='desmontar2-progresso';let P={done:{}};
try{const s=localStorage.getItem(KEY);if(s)P=JSON.parse(s)||P;if(!P.done)P.done={};}catch(e){}
function save(){try{localStorage.setItem(KEY,JSON.stringify(P));}catch(e){}}
const isOpen=(t,i)=>i===0||!!P.done[t+(i)];

/* ---------- estrelas ---------- */
const starSVG=(on,cls='')=>`<svg class="${cls}" viewBox="0 0 24 24"><path fill="${on?'#f5c518':'rgba(255,255,255,.16)'}" d="M12 2l3 6.5 7 .8-5.2 4.8 1.5 7L12 17.6 5.7 21.1l1.5-7L2 9.3l7-.8z"/></svg>`;
const lockSVG='<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2"><rect x="5" y="11" width="14" height="10" rx="2"/><path d="M8 11V8a4 4 0 018 0v3"/></svg>';

/* ---------- sequência de cada trilha: fases + revisões ---------- */
const LV=[['Básico','fases I a III',1,3],['Intermediário','fases IV a VI',4,6],['Avançado','fases VII a IX',7,9],['Desafio','fase X',10,10]];
function nodesOf(t){const out=[];LV.forEach(([nm,sub,a,b],li)=>{out.push({lvl:li,nm,sub});for(let n=a;n<=b;n++)out.push({id:t.id+n,n,ready:n<=t.ready,name:t.ph[n-1]});
  if(li<3)out.push({id:t.id+'R'+(li+1),rev:1,range:[a,b],ready:b<=t.ready,name:`Revisão ${ROMAN[a-1]} a ${ROMAN[b-1]}`});
  else out.push({id:t.id+'R4',rev:1,final:1,range:[1,10],ready:t.ready>=10,name:'Desafio final'});});return out;}
const seqOf=t=>nodesOf(t).filter(x=>x.id);
function nodeOpen(t,id){const s=seqOf(t);const i=s.findIndex(x=>x.id===id);if(i<0||!s[i].ready)return false;return i===0||!!P.done[id]||!!P.done[s[i-1].id];}
const shuffle=a=>{for(let i=a.length-1;i>0;i--){const j=Math.floor(Math.random()*(i+1));[a[i],a[j]]=[a[j],a[i]];}return a;};
function prepReview(id){const t=TRACKS.find(x=>id.startsWith(x.id));const node=seqOf(t).find(x=>x.id===id);if(!node)return;
  const qs=[],learn=[];for(let n=node.range[0];n<=node.range[1];n++){const ph=PH[t.id+n];if(!ph)continue;ph.steps.forEach(s=>{if(s.k==='choose')qs.push(Object.assign({},s,{say:`<b>Da fase ${ROMAN[n-1]}:</b> ${s.say}`}));});learn.push(...ph.learned);}
  const pick=shuffle(qs).slice(0,node.final?8:6).map(s=>Object.assign({},s,{after:null,hint:node.final?null:s.hint}));
  const g=['ar','al','lu','gi'][Math.floor(Math.random()*4)];
  PH[id]={track:t.id,rev:1,final:node.final,title:node.name,build:PH[t.id+node.range[1]].build,
    steps:[{k:'info',g,say:node.final?`<b>Desafio final!</b> ${pick.length} perguntas de toda a trilha, misturadas e <b>sem dicas</b>.`:`Hora de revisar! São ${pick.length} perguntas das fases ${ROMAN[node.range[0]-1]} a ${ROMAN[node.range[1]-1]}, misturadas.`,
      task:node.final?'Responda com calma: cada erro custa estrela.':'Se errar, a explicação aparece na hora.'},...pick],
    learned:shuffle(learn).slice(0,4)};}

/* ---------- tela inicial ---------- */
let VIEW='home';
const totalStars=()=>Object.values(P.done).reduce((a,v)=>a+v,0);
function ring(p,c){const r=20,L=2*PI*r;return `<svg viewBox="0 0 48 48" style="width:100%;height:100%;display:block"><circle cx="24" cy="24" r="${r}" fill="rgba(0,0,0,.25)" stroke="rgba(255,255,255,.18)" stroke-width="5"/><circle cx="24" cy="24" r="${r}" fill="none" stroke="#fff" stroke-width="5" stroke-linecap="round" stroke-dasharray="${L*p} ${L}" transform="rotate(-90 24 24)"/></svg>`;}
function homeHTML(){const z=P.done.zero;let h=`<div class="home"><div class="mtop"><img src="logo.png" alt="" onerror="this.style.display='none'"><h1>DesmontAR 2.0<small>Aprenda montando, em realidade aumentada</small></h1><div class="stars">${starSVG(1)}<span>${totalStars()}</span></div></div>
  <button class="zero" data-go="zero"><div class="ic">0</div><div><b>Como a RA funciona</b><span>Marcador, escala e rastreamento. Comece por aqui!</span></div><div class="st">${z?[1,2,3].map(i=>starSVG(i<=z)).join(''):''}</div></button>
  <p class="sec">Escolha sua trilha</p><div class="grid">`;
  for(const t of TRACKS){const seq=seqOf(t);const done=seq.filter(x=>P.done[x.id]).length;const st=seq.reduce((a,x)=>a+(P.done[x.id]||0),0);const ph=t.ph.filter((_,i)=>P.done[t.id+(i+1)]).length;
    h+=`<button class="tile" style="--c:${t.c}" data-track="${t.id}"><div class="pat"></div><div class="big">${ICON[t.id]}</div><div class="ic">${ICON[t.id]}</div><div class="ring">${ring(done/seq.length)}<b>${Math.round(done/seq.length*100)}%</b></div>
      <h3>${t.name}</h3><p>${t.desc}</p><div class="meta"><i>${ph}/${t.ph.length} fases</i><i>${starSVG(1)} ${st}</i></div></button>`;}
  return h+`</div><p class="mfoot">${TRACKS.filter(t=>t.ready<10).map(t=>t.short).join(' e ')}: fases IV a X em breve · <button id="resetBtn">apagar meu progresso</button></p></div>`;}

/* ---------- uma trilha aberta ---------- */
const ZZ=[0,-70,-104,-70,0,70,104,70];
const backSVG='<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round"><path d="M15 5l-7 7 7 7"/></svg>';
const trophySVG='<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linejoin="round"><path d="M7 4h10v5a5 5 0 01-10 0zM7 6H4a3 3 0 003 4M17 6h3a3 3 0 01-3 4M12 14v4M8 21h8l-1-3H9z"/></svg>';
const reviewSVG='<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round"><path d="M4 12a8 8 0 0114-5.3M20 12a8 8 0 01-14 5.3M18 3v4h-4M6 21v-4h4"/></svg>';
function trackHTML(t){const seq=seqOf(t);const done=seq.filter(x=>P.done[x.id]).length;
  let h=`<div class="tview" style="--c:${t.c}"><div class="tbar"><button class="iconbtn" id="tBack" aria-label="Voltar">${backSVG}</button><div class="ic">${ICON[t.id]}</div><div style="min-width:0"><h2>${t.name}</h2><div class="pb"><i style="width:${done/seq.length*100}%"></i></div></div><div class="stars">${starSVG(1)}<span>${seq.reduce((a,x)=>a+(P.done[x.id]||0),0)}</span></div></div><div class="road"><svg class="line"></svg>`;
  let k=0;const nodes=nodesOf(t);
  for(let d=0;d<6;d++)h+=`<div class="deco" style="width:${90+(d%3)*30}px;height:${90+(d%3)*30}px;top:${120+d*260}px;${d%2?'left':'right'}:${-20+(d%3)*10}px;transform:rotate(${d%2?-14:12}deg)">${ICON[t.id]}</div>`;
  for(const x of nodes){if(x.lvl!=null){h+=`<div class="lvl">${x.nm}<small>${x.sub}</small></div>`;continue;}
    const st=P.done[x.id],open=nodeOpen(t,x.id);const cls=(x.rev?'rev ':'')+(st?'done':open?'open':'');
    const inner=!x.ready||!open?lockSVG:x.rev?(x.final?trophySVG:reviewSVG):st?'✓':ROMAN[x.n-1];
    h+=`<button class="node ${cls}" style="transform:translateX(${ZZ[k++%8]}px)" ${open?`data-go="${x.id}"`:'disabled'} aria-label="${x.rev?x.name:'Fase '+ROMAN[x.n-1]+': '+x.name}${x.ready?'':' (em breve)'}">
      <div class="b"><span>${inner}</span></div><div class="ss">${st?[1,2,3].map(s=>starSVG(s<=st)).join(''):''}</div><div class="nm">${x.rev?x.name:ROMAN[x.n-1]+' · '+x.name}${x.ready?'':'<br><small>em breve</small>'}</div></button>`;}
  return h+'</div></div>';}
function drawRoad(){const road=$('#map .road');if(!road)return;const svg=road.querySelector('svg.line');const r0=road.getBoundingClientRect();
  const pts=[...road.querySelectorAll('.node')].map(n=>{const r=n.querySelector('.b').getBoundingClientRect();return [r.left+r.width/2-r0.left,r.top+r.height/2-r0.top,n.classList.contains('done')];});
  if(pts.length<2)return;const seg=(a,b)=>{const dy=(b[1]-a[1])/2;return `C ${a[0]} ${a[1]+dy} ${b[0]} ${b[1]-dy} ${b[0]} ${b[1]}`;};
  let d=`M ${pts[0][0]} ${pts[0][1]}`,dd=d;let last=0;pts.forEach((p,i)=>{if(i){d+=' '+seg(pts[i-1],p);}if(p[2])last=i;});
  for(let i=1;i<=Math.min(last+1,pts.length-1);i++)if(pts[i-1][2])dd+=' '+seg(pts[i-1],pts[i]);
  svg.innerHTML=`<path d="${d}" fill="none" stroke="rgba(255,255,255,.08)" stroke-width="22" stroke-linecap="round"/><path d="${d}" fill="none" stroke="rgba(255,255,255,.18)" stroke-width="3" stroke-dasharray="2 12" stroke-linecap="round"/>`+(last||pts[0][2]?`<path d="${dd}" fill="none" stroke="var(--c)" stroke-opacity=".75" stroke-width="10" stroke-linecap="round"/>`:'');}
function drawMap(){const m=$('#map');m.innerHTML=VIEW==='home'?homeHTML():trackHTML(TRACKS.find(t=>t.id===VIEW));
  m.querySelectorAll('[data-go]').forEach(b=>b.onclick=()=>openPhase(b.dataset.go));
  m.querySelectorAll('[data-track]').forEach(b=>b.onclick=()=>{VIEW=b.dataset.track;drawMap();m.scrollTop=0;});
  const tb=$('#tBack');if(tb)tb.onclick=()=>{VIEW='home';drawMap();m.scrollTop=0;};
  const rb=$('#resetBtn');if(rb)rb.onclick=()=>{P={done:{}};save();drawMap();toast('Progresso apagado.');};
  if(VIEW!=='home')requestAnimationFrame(()=>{drawRoad();const o=m.querySelector('.node.open');if(o)o.scrollIntoView({block:'center'});});}
addEventListener('resize',()=>{if(VIEW!=='home'&&$('#map').style.display!=='none')drawRoad();});
function setOrd(){const s=G.ph.steps[G.step];G.ord=s.opts?shuffle(s.opts.map((_,i)=>i)):null;}

/* ---------- fases ---------- */
const NAMES={mobo:'a placa-mãe',cpu:'o processador',ram:'a memória RAM',gpu:'a placa de vídeo',ssd:'o SSD',psu:'a fonte',socket:'o soquete do processador',
  A1:'o slot A1',A2:'o slot A2',B1:'o slot B1',B2:'o slot B2',x16:'o slot PCIe x16',x1:'o slot PCIe x1',m2:'o slot M.2',cpuIn:'o processador',
  ard:'o Arduino',proto:'a protoboard',led:'o LED',res:'o resistor',jumper:'o fio jumper',usb:'o cabo USB','13':'o pino 13','12':'o pino 12','11':'o pino 11',GND:'o pino GND','5V':'o pino 5V'};
let bench=new THREE.Group();scene.add(bench);
const R={};/* referências da bancada atual */
function setPick(o,id){o.userData.id=id;return o;}
function addPart(o,id,x,y,z,ly=.45){at(o,x,y,z);setPick(o,id);bench.add(o);R[id]=o;o.userData.ly=ly;return o;}
function showLabel(id,text){const o=R[id];if(!o||o.userData.lab)return;const l=label(text,{size:.15});l.position.set(o.position.x,o.position.y+(o.userData.ly||.45),o.position.z);bench.add(l);o.userData.lab=l;}

const PH={
zero:{track:null,title:'Como a RA funciona',c:'#36d399',
  build(){const g=new THREE.Group();const cube=at(box(.7,.7,.7,0x36d399,{roughness:.35}),0,.6,0);g.add(cube);
    const ring=new THREE.Mesh(new THREE.TorusGeometry(.75,.03,8,64),mat(0xf5c518,{emissive:0x5a4400}));ring.rotation.x=PI/2;ring.position.y=.05;g.add(ring);
    bench.add(g);R.spin=cube;},
  steps:[
    {k:'info',g:'ar',say:'Oi! Antes das trilhas, vamos entender a ferramenta. <b>Realidade aumentada (RA)</b> desenha objetos virtuais por cima da imagem da câmera, como se estivessem na sua mesa.',task:'Para isso o celular precisa saber onde a mesa está. É aí que entra o marcador impresso.'},
    {k:'choose',g:'al',say:'Olhe o marcador: borda preta grossa e quadradinhos pretos e brancos.',task:'Por que o marcador é assim?',
     opts:[{t:'Para a câmera achar os 4 cantos e reconhecer o desenho',ok:1,fb:'A câmera procura o contorno quadrado e lê os quadradinhos, como um QR code. Com os 4 cantos, ela calcula de que ângulo você está olhando.'},
       {t:'Só para ficar bonito',fb:'O desenho não é decoração: cada quadradinho é uma informação que a câmera lê.'},
       {t:'Para a câmera focar melhor',fb:'O foco é automático. O que importa são os cantos e o contraste forte entre preto e branco.'}],
     hint:'Pense em como um QR code é lido.'},
    {k:'ar',g:'lu',say:'Agora na prática. Coloque o marcador impresso na mesa, ligue a RA e aponte a câmera para ele.',task:'Faça a câmera reconhecer o marcador.',hint:'A folha inteira precisa aparecer na tela, com boa luz e sem reflexo.'},
    {k:'choose',g:'gi',say:'O marcador impresso tem 14 cm de lado, e o jogo sabe disso.',task:'Para que o jogo precisa saber o tamanho do marcador?',
     opts:[{t:'Para desenhar os objetos no tamanho certo em cima da mesa',ok:1,fb:'Sabendo o tamanho real, o jogo calcula a distância até a mesa e mantém a escala certa.'},
       {t:'Para saber a cor da mesa',fb:'O tamanho não tem relação com a cor. Ele serve para medir distância e escala.'},
       {t:'Não precisa: o jogo adivinha',fb:'Sem uma medida conhecida, um objeto perto e pequeno parece igual a um longe e grande.'}],hint:'Um objeto perto e pequeno parece igual a um longe e grande.'},
    {k:'choose',g:'ar',say:'A RA refaz a conta da posição muitas vezes por segundo. Isso se chama <b>rastreamento</b>.',task:'Se você tampar o marcador com a mão, o que acontece?',
     opts:[{t:'O objeto some, porque a RA não sabe mais onde desenhar',ok:1,fb:'Sem ver o marcador, a RA perde a referência. Quando ele volta, o objeto reaparece no mesmo lugar.'},
       {t:'O objeto continua igual',fb:'O objeto não está de verdade na mesa: ele só existe na tela, recalculado a partir do marcador.'},
       {t:'O objeto cai da mesa',fb:'Não há física aqui: sem o marcador, a RA simplesmente não sabe onde desenhar.'}],hint:'O objeto não existe de verdade na mesa.'}],
  learned:['A RA desenha objetos virtuais sobre a imagem da câmera','O marcador dá os 4 cantos que a câmera usa como referência','O tamanho conhecido do marcador garante a escala','Sem ver o marcador, o rastreamento se perde']},

hw1:{track:'hw',n:1,title:'Conhecendo as peças',
  build(){const m=mkMobo(false);m.scale.setScalar(.5);addPart(m,'mobo',0,0,-.15,.3);
    addPart(mkCPU(),'cpu',-1.2,.02,-1.35,.3);addPart(mkRAM(true),'ram',1.2,.02,-1.2,.3);const gp=mkGPU();gp.rotation.y=PI/2;addPart(gp,'gpu',1.2,.07,1.15,.35);
    const sd=mkSSD();sd.rotation.y=PI/2;addPart(sd,'ssd',-1.25,.02,-.1,.25);addPart(mkPSU(),'psu',-1.15,0,1.3,.75);},
  steps:[
    ['mobo','a placa-mãe','ar','A placa-mãe é a peça grande onde tudo se conecta. Ela liga processador, memória, placa de vídeo e SSD.','É a maior placa, com vários encaixes.'],
    ['cpu','o processador','al','O processador (CPU) é o cérebro do PC: faz os cálculos. É pequeno, quadrado e tem um triângulo dourado num canto.','Procure a peça pequena e quadrada, com a tampa prateada.'],
    ['ram','a memória RAM','lu','A memória RAM guarda o que está aberto agora. Quando o PC desliga, ela se apaga.','É uma placa comprida e fina, com chips pretos enfileirados.'],
    ['gpu','a placa de vídeo','gi','A placa de vídeo (GPU) desenha as imagens na tela. Nos jogos, é a peça que mais trabalha.','Procure a peça com ventoinhas redondas.'],
    ['ssd','o SSD','ar','O SSD guarda seus arquivos de forma permanente, mesmo com o PC desligado. É bem mais rápido que um HD.','É uma plaquinha preta, comprida e fina, com uma etiqueta.'],
    ['psu','a fonte','al','A fonte transforma a energia da tomada na energia que as peças usam (12 V, 5 V e 3,3 V).','É a caixa com uma grade de ventilação.']].map(([id,n,g,fb,hint])=>(
    {k:'tap',g,say:'Toque na peça que eu pedir. Se errar, eu mostro qual é.',task:`Toque n${n.startsWith('a ')?'a':'o'} ${n.slice(2)}`,ok:id,fb,hint,after(){showLabel(id,n.slice(2)[0].toUpperCase()+n.slice(3));}})),
  learned:['Placa-mãe: liga todas as peças','Processador: faz os cálculos','Memória RAM: guarda o que está aberto','Placa de vídeo: desenha as imagens','SSD: guarda os arquivos','Fonte: alimenta tudo']},

hw2:{track:'hw',n:2,title:'O processador',
  build(){const m=mkMobo(false);addPart(m,'mobo',0,0,0,.3);R.socket=m.children.find(o=>o.userData.id==='socket');
    const c=mkCPU();c.visible=false;bench.add(c);R.cpuNew=c;},
  steps:[
    {k:'choose',g:'ar',say:'A placa-mãe da bancada tem o soquete <b>S5</b>. O soquete é o encaixe do processador.',task:'Qual processador serve nessa placa?',
     opts:[{t:'Processador com soquete S5',s:'Mesmo encaixe da placa',ok:1,fb:'Isso! O processador precisa ter o mesmo soquete da placa-mãe, senão os contatos não batem.'},
       {t:'Processador com soquete S4',s:'Modelo mais antigo',fb:'Os contatos do S4 ficam em outras posições. Ele não encaixa no S5, mesmo sendo parecido.'},
       {t:'Qualquer processador serve',fb:'Cada placa-mãe aceita só os processadores do seu soquete. Por isso essa é a primeira coisa a conferir.'}],hint:'Procure o processador com o mesmo nome do soquete.'},
    {k:'tap',g:'al',say:'Agora vamos colocar o processador no lugar certo da placa.',task:'Toque no soquete do processador',ok:'socket',glow:['socket'],
     fb:'Esse é o soquete. Ele fica perto dos dissipadores de metal, que esfriam a energia que chega ao processador.',hint:'É o quadrado prateado perto das peças de metal.',
     after(){const c=R.cpuNew;c.visible=true;c.position.set(-.3,1.1,-.55);c.rotation.y=PI/2;tween(c,{y:.5},.6);}},
    {k:'choose',g:'lu',say:'Repare no <b>triângulo dourado</b> num canto do processador. O soquete também tem um.',task:'Como encaixar o processador?',
     opts:[{t:'Alinhar o triângulo do processador com o do soquete e soltar sem força',ok:1,fb:'Isso! Com os triângulos alinhados, ele cai no lugar sozinho. Não precisa apertar.'},
       {t:'Girar até entrar, em qualquer posição',fb:'Na posição errada ele não encaixa, e forçar entorta os contatos. Um contato torto pode estragar a placa.'},
       {t:'Apertar com força para firmar',fb:'O processador não precisa de força: ele só apoia no soquete. Quem prende é a alavanca do soquete.'}],hint:'O triângulo serve de guia.',
     after(){const c=R.cpuNew;tween(c,{y:.13,ry:0},.7);setPick(c,'cpuIn');}},
    {k:'choose',g:'gi',say:'Entre o processador e o cooler vai a <b>pasta térmica</b>. Ela preenche os buracos microscópicos entre as duas peças.',task:'Quanto de pasta térmica usar?',
     opts:[{t:'Uma gota do tamanho de um grão de ervilha',ok:1,fb:'Isso! A pressão do cooler espalha a gota sozinha numa camada fina.'},
       {t:'Uma camada bem grossa, cobrindo tudo',fb:'Pasta demais vaza pelas bordas e atrapalha. O que esfria é a camada fina, não a quantidade.'},
       {t:'Não precisa de pasta',fb:'Sem pasta sobra ar entre as peças. O ar conduz mal o calor, e o processador esquenta demais.'}],hint:'Menos é mais.',
     after(){const d=at(new THREE.Mesh(new THREE.SphereGeometry(.05,16,8),mat(0xb8bcc2,{roughness:.3,metalness:.2})),0,.05,0);d.scale.y=.5;R.cpuNew.add(d);}},
    {k:'tap',g:'ar',say:'Por último, o cooler: ele tira o calor do processador e joga para fora.',task:'Toque no processador para colocar o cooler',ok:'cpuIn',
     fb:'Pronto! O cooler apertou a pasta e já está girando. Processador instalado.',hint:'Toque na peça que você acabou de encaixar.',
     after(){const k=mkCooler();k.position.set(-.3,1.3,-.55);bench.add(k);R.cooler=k;tween(k,{y:.24},.8);}}],
  learned:['O soquete do processador precisa ser igual ao da placa','O triângulo dourado mostra a posição certa','Processador não se força: ele cai no lugar','Pasta térmica: uma gota do tamanho de uma ervilha','O cooler tira o calor do processador']},

hw3:{track:'hw',n:3,title:'Memória RAM',
  build(){const m=mkMobo(true);addPart(m,'mobo',0,0,0,.3);m.children.forEach(o=>{if(o.userData.id)R[o.userData.id]=o;});
    const c=mkCPU();at(c,-.3,.13,-.55);m.add(c);const k=mkCooler();at(k,-.3,.24,-.55);m.add(k);R.cooler=k;R.placed={};},
  steps:[
    {k:'choose',g:'lu',say:'Esta placa-mãe só aceita memória <b>DDR5</b>. Cada geração tem um corte (chanfro) num lugar diferente dos contatos.',task:'Qual pente de memória usar?',
     opts:[{t:'Pente DDR5',ok:1,fb:'Isso! O corte do pente bate com o ressalto do slot, então ele encaixa.'},
       {t:'Pente DDR4',fb:'O corte do DDR4 fica em outra posição. Ele não entra no slot DDR5, e forçar quebra o slot.'},
       {t:'Os dois servem',fb:'Cada placa aceita só uma geração de memória. DDR4 e DDR5 não são trocáveis.'}],hint:'Confira o que a placa aceita.'},
    {k:'tap',g:'gi',say:'Você tem <b>2 pentes</b> e a placa tem 4 slots: A1, A2, B1 e B2. O manual da placa manda usar <b>um slot de cada canal</b> (A e B).',task:'Toque no slot do primeiro pente',ok:'A2',glow:['A1','A2','B1','B2'],
     wrong:{A1:'Com 2 pentes, o manual manda começar pelo A2, o slot de cor diferente. O A1 é usado quando há 4 pentes.',B1:'O B1 só é usado com 4 pentes. Com 2, os slots certos são o A2 e o B2.',B2:'Quase! O B2 é para o segundo pente. Comece pelo A2.'},
     fb:'Isso! Primeiro pente no A2.',hint:'Os slots indicados costumam ter outra cor.',after(){placeRAM('A2');}},
    {k:'tap',g:'ar',say:'Agora o segundo pente. Lembre: um pente em cada canal.',task:'Toque no slot do segundo pente',ok:'B2',glow:['A1','B1','B2'],
     wrong:{A1:'Assim os dois pentes ficam no mesmo canal (A) e não trabalham juntos.',B1:'Está no canal certo, mas o manual indica o B2, igual ao A2 no outro canal.',A2:'O A2 já tem um pente.'},
     fb:'Isso! Um pente no canal A e outro no canal B.',hint:'Escolha o slot do canal B com a mesma cor do A2.',after(){placeRAM('B2');}},
    {k:'choose',g:'al',say:'Os dois pentes estão no lugar.',task:'Por que colocar um pente em cada canal?',
     opts:[{t:'Os dois trabalham ao mesmo tempo, e a memória fica mais rápida',s:'Isso se chama dual channel',ok:1,fb:'Isso! Em dual channel, o processador lê os dois pentes ao mesmo tempo, quase dobrando a velocidade.'},
       {t:'Para esfriar melhor',fb:'A distância ajuda um pouco no calor, mas o motivo principal é a velocidade: os dois canais trabalham juntos.'},
       {t:'Não faz diferença',fb:'Faz diferença sim: no mesmo canal, os pentes se revezam em vez de trabalhar juntos.'}],hint:'Pense em duas estradas em vez de uma.'},
    {k:'choose',g:'lu',say:'Última conferência antes de ligar.',task:'Como saber se o pente encaixou direito?',
     opts:[{t:'As travas das pontas fecham sozinhas com um clique',ok:1,fb:'Isso! Se as travas não fecharem, o pente não está todo para dentro. É um dos motivos mais comuns de PC que não liga.'},
       {t:'Ele fica um pouco solto, e isso é normal',fb:'Pente solto é problema: o PC pode nem ligar. Ele precisa ficar firme, com as travas fechadas.'},
       {t:'Só ligando o PC para saber',fb:'Dá para conferir antes: as travas das pontas precisam estar fechadas.'}],hint:'Olhe as pontas do slot.'}],
  learned:['A placa aceita só uma geração de memória (DDR4 ou DDR5)','Com 2 pentes, usar os slots A2 e B2','Um pente em cada canal = dual channel, mais rápido','As travas fechadas mostram que o pente encaixou']},

rb1:{track:'rb',n:1,title:'Conhecendo o Arduino',
  build(){const a=mkArduino();addPart(a,'ard',-.9,0,-.2,.4);const p=mkProto();addPart(p,'proto',.95,0,-.3,.3);
    addPart(mkLED(0xff3b3b),'led',-.35,0,1.15,.45);addPart(mkResistor(),'res',.25,0,1.2,.35);
    const j=new THREE.Group();j.add(wire([[0,.03,0],[.15,.25,.05],[.45,.25,-.05],[.6,.03,0]],0x2fb36b,.02));addPart(j,'jumper',.75,0,1.2,.45);
    addPart(mkUSB(),'usb',-1.35,0,1.35,.35);},
  steps:[
    ['ard','o Arduino','ar','O Arduino é uma placa com um pequeno computador (microcontrolador). Ele roda o seu programa e liga e desliga os pinos.','É a placa azul.'],
    ['proto','a protoboard','al','A protoboard é a placa de montar circuitos sem solda. Os furos de cada coluna são ligados por dentro.','É a placa branca cheia de furinhos.'],
    ['led','o LED','lu','O LED é uma luzinha. Ele só acende num sentido: a perna maior é o positivo (+).','É a peça pequena e vermelha, com duas perninhas.'],
    ['res','o resistor','gi','O resistor segura a corrente. Sem ele, o LED recebe energia demais e queima.','É a pecinha bege com listras coloridas.'],
    ['jumper','o fio jumper','ar','O jumper é o fio que liga o Arduino à protoboard.','É o fio verde.'],
    ['usb','o cabo USB','al','O cabo USB leva o programa do computador para o Arduino e também dá energia a ele.','É o cabo cinza na beira da mesa.']].map(([id,n,g,fb,hint])=>(
    {k:'tap',g,say:'Toque na peça que eu pedir. Se errar, eu mostro qual é.',task:`Toque n${n.startsWith('a ')?'a':'o'} ${n.slice(2)}`,ok:id,fb,hint,after(){showLabel(id,n.slice(2)[0].toUpperCase()+n.slice(3));}})),
  learned:['Arduino: roda o programa e controla os pinos','Protoboard: monta circuitos sem solda','LED: só acende num sentido','Resistor: protege o LED','Jumper: liga as peças','USB: leva o programa e a energia']},

rb2:{track:'rb',n:2,title:'Pisca LED',
  build(){const a=mkArduino();addPart(a,'ard',-.9,0,-.2,.4);R.pins=mkPins(bench,['GND','13','12','5V']);bench.children.forEach(o=>{if(PIN[o.userData.id])R[o.userData.id]=o;});
    const p=mkProto();addPart(p,'proto',.95,0,-.3,.3);const l=mkLED(0xff3b3b);l.visible=false;at(l,.6,.08,-.45);bench.add(l);R.led=l;
    const r=mkResistor();r.visible=false;at(r,1.0,.04,-.45);bench.add(r);R.res=r;},
  steps:[
    {k:'choose',g:'ar',say:'Primeiro projeto de verdade: fazer um LED piscar. O LED tem uma perna maior que a outra.',task:'O que a perna maior indica?',
     opts:[{t:'É o positivo (+), que recebe o sinal do Arduino',ok:1,fb:'Isso! Perna maior no +. Ao contrário, o LED não acende.'},
       {t:'É o negativo (−)',fb:'É o contrário: a perna maior é o positivo. A menor vai para o negativo (GND).'},
       {t:'Tanto faz o lado',fb:'O LED é um diodo: a corrente só passa num sentido. Ao contrário, ele fica apagado.'}],hint:'Maior = mais (+).',
     after(){R.led.visible=true;R.led.position.y=.7;tween(R.led,{y:.08},.6);}},
    {k:'choose',g:'gi',say:'O pino do Arduino solta 5 V. É energia demais para o LED sozinho.',task:'Qual resistor colocar junto do LED?',
     opts:[{t:'220 Ω',s:'Ω (ohm) é a unidade de resistência',ok:1,fb:'Isso! 220 Ω segura a corrente na medida: o LED acende bem e não queima.'},
       {t:'Nenhum, ligar direto',fb:'Sem resistor passa corrente demais. O LED esquenta e queima em segundos.'},
       {t:'1.000.000 Ω (1 MΩ)',fb:'Esse segura corrente demais: quase nada passa, e o LED nem acende.'}],hint:'Nem zero, nem exagero.',
     after(){R.res.visible=true;R.res.position.y=.6;tween(R.res,{y:.04},.6);}},
    {k:'tap',g:'lu',say:'Agora o fio. O sinal sai de um pino e o caminho termina no <b>GND</b>, que é o negativo. O programa vai controlar o <b>pino 13</b>.',task:'Toque no pino 13 do Arduino',ok:'13',glow:['GND','13','12','5V'],
     wrong:{GND:'O GND é o negativo, o fim do caminho. O sinal que liga e desliga sai do pino 13.','5V':'O 5V fica sempre ligado. O LED acenderia, mas nunca piscaria, porque o programa não controla esse pino.','12':'Quase! O programa vai usar o pino 13, logo ao lado.'},
     fb:'Isso! Fio do pino 13 até o LED, e outro fio do LED até o GND. O circuito está fechado.',hint:'Os números estão escritos em cima de cada pino.',
     after(){const p=R.pins;bench.add(wire([[p['13'].x,p['13'].y,p['13'].z],[p['13'].x,.45,p['13'].z+.1],[.35,.4,-.5],[.58,.1,-.45]],0xd23b3b));
       bench.add(wire([[p.GND.x,p.GND.y,p.GND.z],[p.GND.x,.55,p.GND.z+.05],[1.1,.5,-.75],[1.22,.1,-.45]],0x2b2f36));}},
    {k:'code',g:'gi',say:'Hora de programar! Toque nos blocos para montar o programa. O Arduino repete o programa para sempre.',task:'Monte o programa que faz o LED piscar',
     palette:[{id:'on',t:'Ligar LED',c:'on'},{id:'off',t:'Desligar LED',c:'off'},{id:'w1',t:'Esperar 1 s',c:'wait'}],max:6,
     check(p){const s=p.join(',');if(s==='on,w1,off,w1'||s==='off,w1,on,w1')return [1,'O LED liga, espera, desliga, espera e começa de novo. Está piscando!'];
       if(!p.includes('on'))return [0,'O LED nunca liga. Coloque o bloco <b>Ligar LED</b>.'];
       if(!p.includes('off'))return [0,'O LED liga e nunca desliga, então ele fica aceso o tempo todo.'];
       if(!p.includes('w1'))return [0,'Sem esperar, o Arduino liga e desliga milhares de vezes por segundo. Seus olhos veem o LED sempre aceso.'];
       if(p.filter(x=>x==='w1').length<2)return [0,'Falta uma espera. Depois de ligar e depois de desligar, o LED precisa ficar um tempo parado, senão um dos estados passa rápido demais.'];
       return [0,'Quase! Tente a ordem: ligar, esperar, desligar, esperar.'];},
     hint:'Liga → espera → desliga → espera.',fb:'Seu primeiro programa funcionou!'}],
  learned:['A perna maior do LED é o positivo (+)','Resistor de 220 Ω protege o LED','O sinal sai de um pino e volta pelo GND','Sem "esperar", a troca é rápida demais para os olhos']},

rb3:{track:'rb',n:3,title:'Semáforo',
  build(){const a=mkArduino();addPart(a,'ard',-.9,0,-.2,.4);R.pins=mkPins(bench,['GND','13','12','11']);bench.children.forEach(o=>{if(PIN[o.userData.id])R[o.userData.id]=o;});
    const p=mkProto();addPart(p,'proto',.95,0,-.3,.3);
    const cols={r:[0xff3b3b,-.7,'13',0xd23b3b],y:[0xffc21a,-.4,'12',0xe0a800],g:[0x2fe07a,-.1,'11',0x1f9e55]};R.leds={};
    for(const [k,[c,z,pin,wc]] of Object.entries(cols)){const l=mkLED(c);at(l,.6,.08,z);bench.add(l);R.leds[k]=l;const r=mkResistor();at(r,1.0,.04,z);bench.add(r);
      const q=R.pins[pin];bench.add(wire([[q.x,q.y,q.z],[q.x,.4+(-z)*.15,q.z+.1],[.3,.35,z-.05],[.58,.1,z]],wc));}
    const q=R.pins.GND;bench.add(wire([[q.x,q.y,q.z],[q.x,.7,q.z+.05],[1.2,.6,-.9],[1.3,.1,-.8]],0x2b2f36));
    const post=new THREE.Group();post.add(at(cyl(.05,1.3,0x2b2f36),0,.65,0));post.add(at(box(.34,.9,.26,0x1a1d22),0,1.6,0));
    R.lamps={};[['r',1.88],['y',1.6],['g',1.32]].forEach(([k,y])=>{const lc=R.leds[k].userData.color;const m=new THREE.Mesh(new THREE.SphereGeometry(.1,20,12),mat(lc,{emissive:new THREE.Color(lc).multiplyScalar(.06)}));m.position.set(0,y,.12);post.add(m);R.lamps[k]=m;});
    post.position.set(1.5,0,.75);bench.add(post);},
  steps:[
    {k:'choose',g:'ar',say:'Agora 3 LEDs: vermelho, amarelo e verde. Vamos programar um semáforo de carros.',task:'Qual é a ordem das cores de um semáforo no Brasil?',
     opts:[{t:'Verde → amarelo → vermelho → verde de novo',ok:1,fb:'Isso! O amarelo avisa que vai fechar. Depois do vermelho, volta direto o verde.'},
       {t:'Verde → vermelho → amarelo',fb:'O amarelo vem antes do vermelho, para avisar os motoristas que o sinal vai fechar.'},
       {t:'Vermelho → amarelo → verde',fb:'Em alguns países é assim, mas no Brasil o vermelho vai direto para o verde.'}],hint:'O amarelo é um aviso.'},
    {k:'choose',g:'al',say:'Cada luz fica acesa por um tempo diferente.',task:'Qual luz fica acesa por menos tempo?',
     opts:[{t:'O amarelo',ok:1,fb:'Isso! O amarelo só avisa que vai fechar, por isso dura pouco.'},{t:'O verde',fb:'O verde precisa durar bastante para os carros passarem.'},{t:'O vermelho',fb:'O vermelho dura bastante para os pedestres e a outra rua passarem.'}],hint:'Qual delas é só um aviso?'},
    {k:'tap',g:'lu',say:'Cada LED está ligado num pino diferente. Os fios têm a mesma cor do LED.',task:'Siga o fio do LED vermelho e toque no pino dele',ok:'13',glow:['GND','13','12','11'],
     wrong:{'12':'O pino 12 é o fio amarelo. Siga o fio vermelho.','11':'O pino 11 é o fio verde. Siga o fio vermelho.',GND:'O GND é o caminho de volta, comum aos três LEDs.'},
     fb:'Isso! Vermelho no 13, amarelo no 12 e verde no 11. No programa, cada bloco liga um desses pinos.',hint:'Gire a bancada para ver melhor os fios.'},
    {k:'code',g:'gi',say:'Agora monte o programa. Quando uma luz acende, as outras apagam. O programa repete para sempre.',task:'Programe o semáforo',
     palette:[{id:'g',t:'Verde acende',c:'g'},{id:'y',t:'Amarelo acende',c:'y'},{id:'r',t:'Vermelho acende',c:'r'},{id:'w5',t:'Esperar 5 s',c:'wait'},{id:'w2',t:'Esperar 2 s',c:'wait'}],max:8,
     check(p){const pairs=[];for(let i=0;i<p.length;i++){if('gyr'.includes(p[i])){const w=p[i+1];if(w!=='w5'&&w!=='w2')return [0,'Toda luz precisa de um <b>Esperar</b> logo depois. Sem isso, ela troca rápido demais.'];pairs.push(p[i]+w);i++;}else return [0,'Cada <b>Esperar</b> precisa vir logo depois de uma luz.'];}
       const want=['gw5','yw2','rw5'];const cols=pairs.map(x=>x[0]).join('');
       if(pairs.length!==3||!['gyr','yrg','rgy'].includes(cols))return [0,'Confira as cores: use cada luz uma vez, na ordem verde → amarelo → vermelho.'];
       const rot=cols==='gyr'?0:cols==='yrg'?1:2;const ok=pairs.every((x,i)=>x===want[(i+rot)%3]);
       if(ok)return [1,'Verde por 5 s, amarelo por 2 s, vermelho por 5 s, e começa de novo. É um semáforo de verdade!'];
       if(pairs.find(x=>x[0]==='y')!=='yw2')return [0,'O amarelo está durando demais. Ele é só um aviso: use <b>Esperar 2 s</b>.'];
       return [0,'Verde e vermelho precisam de mais tempo, para os carros passarem: use <b>Esperar 5 s</b>.'];},
     hint:'Verde (5 s) → amarelo (2 s) → vermelho (5 s).',fb:'Semáforo funcionando!'},
    {k:'choose',g:'ar',say:'Um teste de manutenção, como na vida real.',task:'Se o fio do pino 12 se soltar, o que acontece?',
     opts:[{t:'O amarelo nunca acende, e o resto funciona',ok:1,fb:'Isso! Cada LED tem seu próprio pino e seu próprio caminho. Só o amarelo para.'},
       {t:'O semáforo inteiro apaga',fb:'Cada LED tem seu próprio pino. Só o caminho do amarelo foi interrompido.'},
       {t:'O vermelho começa a piscar',fb:'O pino 12 é só do amarelo. O vermelho continua no pino 13, sem mudança.'}],hint:'Qual cor está no pino 12?'}],
  learned:['Vários LEDs, cada um no seu pino','Ordem do semáforo: verde → amarelo → vermelho','O amarelo dura menos porque é um aviso','Seguir os fios ajuda a achar defeitos']}
};
function placeRAM(k){const s=mkRAM(false);s.position.set(RAMX[k],1.1,-.55);bench.add(s);tween(s,{y:.27},.6);R.placed[k]=1;}

/* ---------- trilha 3: eletrônica básica ---------- */
function wp(o,x,y,z){o.updateMatrixWorld(true);return o.localToWorld(new THREE.Vector3(x,y,z)).toArray();}
function W(a,b,col=0xd23b3b,h=.25){const m=arcWire(a,b,col,h,.016);bench.add(m);return m;}
function flowOn(m,col=0xffd34d,n=4,sp=.35){return addFlow(m.userData.curve,col,n,sp);}
function fadeTo(obj,from,to,dur,setter){let t=0;R.updaters.push(dt=>{if(t>=dur)return;t=Math.min(dur,t+dt);setter(from+(to-from)*(t/dur));});}
function lift(o,dy=1.2){tween(o,{y:o.position.y+dy},.6);setTimeout(()=>{o.visible=false;},650);}
Object.assign(NAMES,{bat:'a pilha',bulb:'a lâmpada',sw:'o interruptor',cap:'o capacitor',tr:'o transistor',motor:'o motor',pot:'o potenciômetro',btn:'o botão',mm:'o multímetro',
  r220:'o resistor de 220 Ω',r1k:'o resistor de 1 kΩ',r10k:'o resistor de 10 kΩ',serie:'o circuito em série',paralelo:'o circuito em paralelo',railP:'a fileira do +',
  c5top:'um furo da coluna 5',c12a:'o furo da coluna 12',c5bot:'a coluna 5 do outro lado',short:'o fio do curto',w2:'o fio do resistor',led1:'o LED 1',led2:'o LED 2',
  E:'a perna E (emissor)',B:'a perna B (base)',C:'a perna C (coletor)',dcv:'a posição V⎓',acv:'a posição V~',ohm:'a posição Ω',cont:'a posição de continuidade',a:'a posição A',off:'a posição OFF',chart:'a tabela de cores'});
const zone=(id,w,d,x,y,z)=>{const m=at(box(w,.03,d,mat(0,{transparent:true,opacity:0,depthWrite:false})),x,y,z);m.userData.id=id;bench.add(m);R[id]=m;return m;};
const colorChart=()=>canvasTex(640,700,(c,w,h)=>{c.fillStyle='#f4f2ec';rrect(c,0,0,w,h,24);c.fill();txt(c,'Código de cores',w/2,46,38,'#14181e','center',800);
  [['preto','#111',0],['marrom','#7a4a24',1],['vermelho','#d23b3b',2],['laranja','#f08a24',3],['amarelo','#f5c518',4],['verde','#2fa65a',5],['azul','#2b62c9',6],['violeta','#8a4fd1',7],['cinza','#8b8f97',8],['branco','#fff',9]].forEach(([n,col,d],i)=>{
    const y=96+i*46;c.fillStyle=col;rrect(c,40,y,70,34,6);c.fill();c.strokeStyle='#999';c.lineWidth=1;c.stroke();txt(c,n,130,y+18,26,'#14181e','left',600);txt(c,String(d),330,y+18,30,'#14181e','center',800);txt(c,'×'+(10**d).toLocaleString('pt-BR'),480,y+18,24,'#4b5563','center',600);});
  txt(c,'1ª e 2ª faixa: algarismos · 3ª: multiplica',w/2,h-36,22,'#4b5563','center',700);},'chart');

Object.assign(PH,{
el1:{track:'el',n:1,title:'O circuito fechado',
  build(){const b=mkBattery();addPart(b,'bat',-1.05,0,-.3,1.15);const l=mkBulb();l.scale.setScalar(2.1);addPart(l,'bulb',.95,0,-.35,1.05);const s=mkSwitch();s.scale.setScalar(1.6);addPart(s,'sw',0,0,.75,.55);
    R.w1=W(wp(b,-.1,.86,0),wp(s,-.11,.12,0),0xd23b3b,.35);R.w2=W(wp(s,.11,.12,0),wp(l,-.12,.12,0),0xd23b3b,.3);
    R.loose=W(wp(l,.12,.12,0),[.35,.02,-1.25],0x22262c,.2);R.a=wp(l,.12,.12,0);R.m=wp(b,.1,.86,0);l.userData.set(0);},
  steps:[
    {k:'choose',g:'ar',say:'Bem-vinda à eletrônica! Aqui tem uma <b>pilha</b>, uma <b>lâmpada</b> e um <b>interruptor</b> ligados por fios. Mas a lâmpada não acende.',task:'Por que a lâmpada está apagada?',
     opts:[{t:'Um fio está solto, então o caminho está aberto',ok:1,fb:'Isso! A corrente só anda num caminho fechado, que sai da pilha e volta para ela. Com um fio solto, nada passa.'},
       {t:'A pilha está fraca',fb:'Pode acontecer, mas aqui olhe os fios: um deles está solto na mesa.'},{t:'A lâmpada é pequena demais',fb:'O tamanho não importa. Siga os fios: um deles não chega na pilha.'}],hint:'Siga os fios com o dedo.',
     after(){bench.remove(R.loose);R.wc=W(R.a,R.m,0x22262c,.45);R.bulb.userData.set(1);}},
    {k:'tap',g:'al',say:'Circuito fechado: a lâmpada acendeu! Agora vamos desligar sem tirar nenhum fio.',task:'Toque no interruptor para desligar',ok:'sw',
     fb:'Isso! O interruptor abre o caminho por dentro. Sem caminho, a corrente para e a lâmpada apaga.',hint:'É a peça com a alavanquinha.',after(){R.sw.userData.set(false);R.bulb.userData.set(0);}},
    {k:'choose',g:'lu',say:'Vamos ligar de novo e seguir a corrente.',task:'Que caminho a corrente faz?',
     opts:[{t:'Sai do + da pilha, passa pelo interruptor e pela lâmpada e volta ao −',ok:1,fb:'Isso! É um caminho em volta, por isso se chama <b>circuito</b>. As bolinhas mostram esse caminho.'},
       {t:'Sai dos dois lados da pilha e se encontra na lâmpada',fb:'A corrente faz uma volta só: sai por um lado e volta pelo outro.'},{t:'Fica parada dentro da lâmpada',fb:'A corrente precisa circular o tempo todo. Se o caminho abre, ela para.'}],hint:'Circuito vem de círculo.',
     after(){R.sw.userData.set(true);R.bulb.userData.set(1);[R.w1,R.w2,R.wc].forEach(w=>flowOn(w));}},
    {k:'choose',g:'gi',say:'Os fios são de cobre, coberto de plástico.',task:'E se trocar um fio por um barbante?',
     opts:[{t:'A lâmpada apaga: barbante não deixa a corrente passar',ok:1,fb:'Isso! Barbante, plástico e borracha são <b>isolantes</b>. Cobre e outros metais são <b>condutores</b>.'},
       {t:'A lâmpada acende mais fraco',fb:'Barbante não conduz nada: o caminho fica aberto, como um fio solto.'},{t:'Nada muda',fb:'Muda sim: barbante é isolante e interrompe o caminho.'}],hint:'O plástico do fio está lá para proteger você.'}],
  learned:['Corrente só passa em caminho fechado','O interruptor abre e fecha o caminho','A corrente sai do + e volta ao −','Metais conduzem; plástico e barbante isolam']},

el2:{track:'el',n:2,title:'Protoboard',
  build(){const p=mkProto();p.scale.setScalar(2);addPart(p,'proto',0,0,0,.3);const l=mkLED(0xff3b3b);l.scale.setScalar(1.2);at(l,-.973,.16,-.626);bench.add(l);
    const lb=label('LED aqui',{size:.12});lb.position.set(-.973,.6,-.66);bench.add(lb);
    zone('c5top',.12,.32,-.973,.17,-.41);zone('c12a',.14,.14,-.337,.17,-.626);zone('c5bot',.12,.42,-.973,.17,.555);},
  steps:[
    {k:'choose',g:'lu',say:'A <b>protoboard</b> serve para montar circuitos sem solda: é só encaixar as perninhas nos furos.',task:'Para que servem as fileiras das bordas, com linha vermelha e azul?',
     opts:[{t:'Levar o positivo (+) e o negativo (−) para a placa toda',ok:1,fb:'Isso! A fileira da linha vermelha é o + e a da azul é o −. Assim qualquer peça pega energia por perto.'},
       {t:'São só decoração',fb:'As linhas mostram onde ligar o + (vermelha) e o − (azul) da pilha.'},{t:'Para encaixar o Arduino',fb:'O Arduino fica fora. As bordas distribuem o + e o − pela placa.'}],hint:'Vermelho e azul são as cores do + e do −.'},
    {k:'tap',g:'gi',say:'Por dentro, os furos são ligados por tirinhas de metal. O LED está no furo da <b>coluna 5, fileira a</b>.',task:'Toque num furo ligado ao LED por dentro',ok:'c5top',
     wrong:{c12a:'Esse furo está na mesma fileira (a), mas em outra coluna. Por dentro, quem se liga são os 5 furos da mesma coluna: de a até e.',c5bot:'É a mesma coluna, mas do outro lado do canal do meio. O canal separa as duas metades.',proto:'Toque num furo perto do LED.'},
     fb:'Isso! Os furos a, b, c, d e e da mesma coluna são ligados por uma tira de metal. A tira amarela mostra isso.',hint:'Desça pela mesma coluna do LED, sem passar o canal do meio.',
     after(){bench.add(at(box(.07,.012,.42,mat(0xf5c518,{emissive:0xf5c518,emissiveIntensity:.6,transparent:true,opacity:.75})),-.973,.17,-.45));}},
    {k:'choose',g:'ar',say:'No meio da placa tem um canal que divide as duas metades.',task:'Para que serve o canal do meio?',
     opts:[{t:'Para encaixar chips, com uma fileira de pernas de cada lado',ok:1,fb:'Isso! Assim cada perna do chip fica numa coluna diferente, sem ligar uma na outra.'},
       {t:'Para ventilar a placa',fb:'A protoboard quase não esquenta. O canal separa os lados para os chips.'},{t:'Para dobrar a placa',fb:'Ela não dobra. O canal existe para encaixar chips no meio.'}],hint:'Pense num chip com duas fileiras de pernas.'},
    {k:'choose',g:'al',say:'Agora um erro muito comum.',task:'E se as duas pernas do LED ficarem na mesma coluna?',
     opts:[{t:'Ele não acende: as duas pernas ficam ligadas entre si',ok:1,fb:'Isso! A corrente pula de uma perna para a outra pela tira de metal, sem passar pelo LED. Cada perna vai numa coluna.'},
       {t:'Ele acende mais forte',fb:'Ao contrário: a corrente desvia pela tira e o LED fica apagado.'},{t:'Não faz diferença',fb:'Faz diferença: na mesma coluna, as pernas ficam em curto e o LED não acende.'}],hint:'Lembre que a coluna inteira é ligada por dentro.'}],
  learned:['Bordas: + (vermelha) e − (azul)','Os 5 furos de uma coluna são ligados','O canal do meio separa as metades','Cada perna do LED vai numa coluna']},

el3:{track:'el',n:3,title:'Resistor',
  build(){[['r220',['red','red','brown'],-1.15],['r1k',['brown','black','red'],-.7],['r10k',['brown','black','orange'],-.25]].forEach(([id,b,z])=>{const r=mkResistor(b);r.scale.setScalar(2.1);addPart(r,id,0,0,z,.45);});
    const ch=decal(1.35,1.48,colorChart(),.004,{transparent:false});const cg=new THREE.Group();cg.add(ch);addPart(cg,'chart',0,0,.75,.2);},
  steps:[
    {k:'choose',g:'gi',say:'O <b>resistor</b> é uma das peças mais usadas em eletrônica.',task:'Para que serve o resistor?',
     opts:[{t:'Para limitar a corrente que passa no circuito',ok:1,fb:'Isso! Ele "segura" a corrente, como um cano mais fino segura a água.'},{t:'Para guardar energia',fb:'Quem guarda energia é o capacitor (fase VII). O resistor limita a corrente.'},{t:'Para acender',fb:'Ele não acende. Ele controla quanta corrente chega nas outras peças.'}],hint:'Resistir = segurar.'},
    {k:'tap',g:'ar',say:'O valor do resistor vem pintado em faixas coloridas. Use a tabela da mesa.',task:'Toque no resistor de 220 Ω (vermelho, vermelho, marrom)',ok:'r220',
     wrong:{r1k:'Marrom, preto, vermelho = 1, 0 e ×100 = 1.000 Ω (1 kΩ).',r10k:'Marrom, preto, laranja = 1, 0 e ×1.000 = 10.000 Ω (10 kΩ).',chart:'Essa é a tabela. Use ela para ler as faixas dos resistores.'},
     fb:'Isso! Vermelho (2), vermelho (2) e marrom (×10) = 220 Ω.',hint:'Procure duas faixas vermelhas seguidas.'},
    {k:'choose',g:'lu',say:'Agora você lê sozinha.',task:'Quanto vale marrom, preto, vermelho?',
     opts:[{t:'1.000 Ω (1 kΩ)',ok:1,fb:'Isso! 1 e 0 formam 10, e o vermelho multiplica por 100: 1.000 Ω.'},{t:'100 Ω',fb:'Quase: 10 × 100 = 1.000. O vermelho multiplica por 100.'},{t:'102 Ω',fb:'A 3ª faixa não é algarismo: ela multiplica. 10 × 100 = 1.000 Ω.'}],hint:'A 3ª faixa diz quantos zeros pôr no fim.'},
    {k:'choose',g:'al',say:'Por que tanto cuidado com o valor?',task:'O que acontece com um LED ligado sem resistor?',
     opts:[{t:'Passa corrente demais e ele queima',ok:1,fb:'Isso! Sem resistor nada segura a corrente, e o LED esquenta e queima em segundos.'},{t:'Fica mais bonito',fb:'Ele até brilha forte por um instante, mas logo queima.'},{t:'Não acende',fb:'Ele acende, mas com corrente demais, e queima.'}],hint:'O resistor é a proteção do LED.'},
    {k:'choose',g:'gi',say:'Última faixa: a dourada.',task:'Para que serve a faixa dourada?',
     opts:[{t:'Mostra a margem de erro do valor: 5%',ok:1,fb:'Isso! Um resistor de 220 Ω com faixa dourada pode ter entre 209 e 231 Ω.'},{t:'Diz que ele é de ouro',fb:'É só tinta. Ela indica a tolerância, a margem de erro de 5%.'},{t:'Multiplica por 1.000',fb:'Quem multiplica é a 3ª faixa. A dourada é a margem de erro.'}],hint:'Nenhum resistor sai de fábrica perfeito.'}],
  learned:['O resistor limita a corrente','1ª e 2ª faixa: algarismos; 3ª: multiplicador','Vermelho-vermelho-marrom = 220 Ω','Faixa dourada: 5% de margem']},

el4:{track:'el',n:4,title:'Série e paralelo',
  build(){const mk=(id,cx,par)=>{const g=new THREE.Group();g.userData.id=id;bench.add(g);R[id]=g;g.position.set(cx,0,0);g.updateMatrixWorld(true);
      const b=mkBattery();b.scale.setScalar(.7);at(b,0,0,-.75);g.add(b);const l1=mkBulb();l1.scale.setScalar(1.35);at(l1,-.4,0,.35);g.add(l1);const l2=mkBulb();l2.scale.setScalar(1.35);at(l2,.4,0,.35);g.add(l2);
      const P=(o,x,y,z)=>wp(o,x,y,z);const a=(arr)=>g.add(arcWire(arr[0],arr[1],arr[2]||0xd23b3b,.22,.014));const bP=P(b,-.1,.86,0),bM=P(b,.1,.86,0);
      const toLocal=v=>g.worldToLocal(new THREE.Vector3(...v)).toArray();
      if(!par){a([toLocal(bP),toLocal(P(l1,-.12,.12,0))]);a([toLocal(P(l1,.12,.12,0)),toLocal(P(l2,-.12,.12,0))]);a([toLocal(P(l2,.12,.12,0)),toLocal(bM),0x22262c]);l1.userData.set(.35);l2.userData.set(.35);}
      else{a([toLocal(bP),toLocal(P(l1,-.12,.12,0))]);a([toLocal(bP),toLocal(P(l2,-.12,.12,0))]);a([toLocal(P(l1,.12,.12,0)),toLocal(bM),0x22262c]);a([toLocal(P(l2,.12,.12,0)),toLocal(bM),0x22262c]);l1.userData.set(1);l2.userData.set(1);}
      g.userData.l=[l1,l2];};
    mk('serie',-.95,false);mk('paralelo',.95,true);},
  steps:[
    {k:'tap',g:'lu',say:'Dois circuitos com as mesmas peças, ligadas de jeitos diferentes. Em <b>série</b>, as lâmpadas ficam uma depois da outra, num caminho só.',task:'Toque no circuito em série',ok:'serie',
     wrong:{paralelo:'Esse é o paralelo: cada lâmpada tem seu próprio caminho até a pilha.'},fb:'Isso! Siga o fio: ele passa pela primeira lâmpada e só depois pela segunda.',hint:'Procure onde um fio liga uma lâmpada direto na outra.',after(){showLabel('serie','Série');showLabel('paralelo','Paralelo');}},
    {k:'choose',g:'ar',say:'Repare no brilho: em série as lâmpadas estão bem mais fracas.',task:'Por que as lâmpadas em série brilham menos?',
     opts:[{t:'A tensão da pilha se divide entre as duas lâmpadas',ok:1,fb:'Isso! Cada lâmpada fica com metade dos 9 V. No paralelo, cada uma recebe os 9 V inteiros.'},{t:'A pilha da série é mais fraca',fb:'As pilhas são iguais. A diferença é o jeito de ligar.'},{t:'Uma lâmpada rouba a luz da outra',fb:'Não é a luz que se divide, é a tensão da pilha.'}],hint:'Pense em dividir os 9 V.'},
    {k:'choose',g:'al',say:'Vamos testar um defeito.',task:'Se uma lâmpada da série queimar, o que acontece?',
     opts:[{t:'As duas apagam, porque o único caminho se abre',ok:1,fb:'Isso! Em série existe um caminho só. Tirou uma peça, o caminho abriu e tudo apaga.'},{t:'A outra fica mais forte',fb:'No circuito em série, sem a lâmpada o caminho abre e as duas apagam.'},{t:'Nada muda',fb:'Muda: o caminho é um só, então a outra lâmpada também apaga.'}],hint:'Lembre do fio solto da fase I.',
     after(){const[a,b]=R.serie.userData.l;lift(b,1.0);a.userData.set(0);}},
    {k:'choose',g:'gi',say:'Pense na sua casa: quando uma lâmpada queima, as outras continuam acesas.',task:'Então as lâmpadas e tomadas de casa são ligadas em…',
     opts:[{t:'Paralelo',ok:1,fb:'Isso! Cada aparelho tem seu caminho e recebe a tensão inteira da rede (127 V ou 220 V).'},{t:'Série',fb:'Se fosse em série, uma lâmpada queimada apagaria a casa toda.'},{t:'Depende do dia',fb:'A instalação é sempre em paralelo, para cada aparelho funcionar sozinho.'}],hint:'Uma lâmpada queimada não apaga a casa.'}],
  learned:['Série: um caminho só, a tensão se divide','Paralelo: cada peça tem seu caminho','Em série, uma peça queimada apaga tudo','A instalação de casa é em paralelo']},

el5:{track:'el',n:5,title:'Lei de Ohm',
  build(){const b=mkBattery();addPart(b,'bat',-1.15,0,-.45,1.15);const r=mkResistor(['yellow','green','brown']);r.scale.setScalar(2.4);addPart(r,'res',0,0,-.75,.55);
    const m=mkMultimeter();addPart(m,'mm',.95,0,.0,.4);m.userData.setDial('a');m.userData.setLCD('-- mA');
    W(wp(b,-.1,.86,0),wp(r,-.3,0,0),0xd23b3b,.3);W(wp(r,.3,0,0),wp(m,0,.15,.46),0xd23b3b,.3);W(wp(m,-.18,.15,.46),wp(b,.1,.86,0),0x22262c,.5);
    const f=canvasTex(512,256,(c,w,h)=>{c.fillStyle='#f4f2ec';rrect(c,0,0,w,h,20);c.fill();txt(c,'V = R × I',w/2,80,72,'#14181e','center',800);txt(c,'tensão (V) = resistência (Ω) × corrente (A)',w/2,170,22,'#4b5563','center',700);},'ohm');
    const fg=new THREE.Group();fg.add(decal(1.3,.65,f,.004,{transparent:false}));at(fg,-.6,0,.95);bench.add(fg);},
  steps:[
    {k:'info',g:'ar',say:'A <b>Lei de Ohm</b> junta três medidas: <b>tensão</b> (V, em volts), <b>resistência</b> (R, em ohms) e <b>corrente</b> (I, em ampères). A regra é <b>V = R × I</b>.',task:'O multímetro está medindo a corrente do circuito. Vamos calcular antes de olhar.'},
    {k:'choose',g:'lu',say:'A pilha tem 9 V e o resistor tem 450 Ω (amarelo, verde, marrom).',task:'Qual é a corrente? (I = V ÷ R)',
     opts:[{t:'0,02 A, ou seja, 20 mA',ok:1,fb:'Isso! 9 ÷ 450 = 0,02 A. Como 1 A = 1.000 mA, são 20 mA. Olhe o multímetro.'},{t:'4.050 A',fb:'Isso seria multiplicar. Para achar a corrente, divida: 9 ÷ 450.'},{t:'2 mA',fb:'Confira a conta: 9 ÷ 450 = 0,02 A = 20 mA.'}],hint:'Divida a tensão pela resistência.',after(){R.mm.userData.setLCD('20.0 mA');}},
    {k:'choose',g:'gi',say:'Agora o caso do LED no Arduino: o pino dá 5 V, o LED usa 2 V e sobram 3 V para o resistor. Queremos 15 mA (0,015 A).',task:'Qual resistor usar? (R = V ÷ I)',
     opts:[{t:'200 Ω',ok:1,fb:'Isso! 3 ÷ 0,015 = 200 Ω. Na loja, o valor mais perto é 220 Ω, que deixa a corrente um pouco menor.'},{t:'20 Ω',fb:'Confira a conta: 3 ÷ 0,015 = 200. Com 20 Ω passaria corrente demais.'},{t:'2.000 Ω',fb:'Com 2.000 Ω a corrente seria 1,5 mA, e o LED ficaria bem fraco.'}],hint:'Use 3 V, não 5 V.'},
    {k:'choose',g:'al',say:'Voltando ao circuito da mesa.',task:'Se a resistência dobrar (450 → 900 Ω), a corrente…',
     opts:[{t:'Cai pela metade',ok:1,fb:'Isso! 9 ÷ 900 = 0,01 A = 10 mA. Mais resistência, menos corrente.'},{t:'Dobra também',fb:'É o contrário: resistência maior segura mais a corrente.'},{t:'Não muda',fb:'Muda: 9 ÷ 900 = 10 mA, metade de antes.'}],hint:'Resistência segura a corrente.',after(){R.mm.userData.setLCD('10.0 mA');}},
    {k:'choose',g:'ar',say:'Para fechar.',task:'Qual é a unidade de medida da corrente elétrica?',
     opts:[{t:'Ampère (A)',ok:1,fb:'Isso! Volt para tensão, ohm para resistência e ampère para corrente.'},{t:'Volt (V)',fb:'Volt mede tensão. A corrente se mede em ampères.'},{t:'Watt (W)',fb:'Watt mede potência, que é tensão × corrente.'}],hint:'O "A" do multímetro.'}],
  learned:['V = R × I','I = V ÷ R e R = V ÷ I','Mais resistência, menos corrente','1 A = 1.000 mA']},

el6:{track:'el',n:6,title:'Multímetro',
  build(){const m=mkMultimeter();m.scale.setScalar(1.3);addPart(m,'mm',-.55,0,0,.4);for(const [k,s] of Object.entries(m.userData.spots)){s.userData.id=k;R[k]=s;}
    const b=mkBattery();addPart(b,'bat',1.15,0,-.45,1.15);R.pr=probe(0xd23b3b,wp(m,0,.15,.46),[.3,.03,.9]);R.pb=probe(0x22262c,wp(m,-.18,.15,.46),[-.1,.03,1.05]);bench.add(R.pr,R.pb);},
  steps:[
    {k:'tap',g:'lu',say:'O <b>multímetro</b> mede tensão, corrente e resistência. Primeiro escolha o que medir no seletor redondo. Vamos medir a bateria de 9 V.',task:'Toque na posição para tensão contínua (V⎓)',ok:'dcv',glow:['off','dcv','acv','ohm','cont','a'],
     wrong:{acv:'V~ é tensão alternada, a da tomada. Pilhas e baterias dão tensão contínua: V⎓.',ohm:'Ω mede resistência, não tensão.',cont:'♪ é a continuidade: apita quando o caminho está fechado.',a:'A mede corrente, e precisa de outra ligação.',off:'OFF desliga o aparelho.'},
     fb:'Isso! V⎓ (com a linha reta) é tensão contínua, que é a de pilhas, baterias e do Arduino.',hint:'Procure o V com uma linha reta.',after(){R.mm.userData.setDial('dcv');R.mm.userData.setLCD('0.00');}},
    {k:'choose',g:'gi',say:'Seletor no lugar. Agora as pontas de prova.',task:'Onde encostar as pontas?',
     opts:[{t:'Vermelha no + e preta no −',ok:1,fb:'Isso! Vermelho no positivo e preto no negativo, sempre.'},{t:'As duas no +',fb:'Assim não há diferença para medir: o visor mostra 0. Uma ponta em cada terminal.'},{t:'Vermelha no − e preta no +',fb:'O valor sai negativo (−9 V). Funciona, mas o certo é vermelho no +.'}],hint:'Vermelho = +.',
     after(){bench.remove(R.pr,R.pb);const b=R.bat;R.pr=probe(0xd23b3b,wp(R.mm,0,.15,.46),wp(b,-.1,.92,-.3));R.pb=probe(0x22262c,wp(R.mm,-.18,.15,.46),wp(b,.1,.92,-.3));bench.add(R.pr,R.pb);R.mm.userData.setLCD('6.80');}},
    {k:'choose',g:'ar',say:'O visor mostra <b>6,80 V</b>.',task:'Uma bateria de 9 V medindo 6,8 V está…',
     opts:[{t:'Fraca, perto de acabar',ok:1,fb:'Isso! Nova, ela marca uns 9,5 V. Abaixo de 7 V, quase nada funciona direito.'},{t:'Ótima',fb:'Ela deveria marcar perto de 9 V. Com 6,8 V está fraca.'},{t:'Queimada',fb:'Queimada marcaria perto de 0. Com 6,8 V ela ainda tem um pouco de carga.'}],hint:'Compare com os 9 V do rótulo.'},
    {k:'tap',g:'al',say:'Outro uso muito comum: testar se um fio está partido por dentro.',task:'Escolha a continuidade (♪)',ok:'cont',glow:['off','dcv','acv','ohm','cont','a'],
     wrong:{dcv:'V⎓ mede tensão. Para testar fio, use a continuidade (♪).',ohm:'Ω até funciona, mas a continuidade (♪) é mais prática: ela apita.',acv:'V~ é tensão da tomada.',a:'A mede corrente.',off:'OFF desliga o aparelho.'},
     fb:'Isso! Encoste uma ponta em cada lado do fio: se apitar, o caminho está inteiro.',hint:'O símbolo de som.',after(){R.mm.userData.setDial('cont');R.mm.userData.setLCD('beep');}},
    {k:'choose',g:'lu',say:'Última dica de uso.',task:'Para medir corrente, como ligar o multímetro?',
     opts:[{t:'Em série, no meio do caminho da corrente',ok:1,fb:'Isso! A corrente precisa passar por dentro do multímetro. Tensão se mede em paralelo; corrente, em série.'},{t:'Em paralelo, nas pontas da peça',fb:'Em paralelo se mede tensão. Para corrente, abra o circuito e ligue o multímetro no meio.'},{t:'Encostando só uma ponta',fb:'Com uma ponta só, não há caminho. A corrente precisa passar pelo aparelho.'}],hint:'A corrente tem que atravessar o aparelho.'}],
  learned:['V⎓ para pilhas; V~ para tomada','Vermelha no + e preta no −','Continuidade (♪) testa fios','Corrente se mede em série']},

el7:{track:'el',n:7,title:'Capacitor',
  build(){const b=mkBattery();addPart(b,'bat',-1.15,0,-.35,1.15);const s=mkSwitch();s.scale.setScalar(1.6);addPart(s,'sw',-.3,0,.75,.55);
    const c=mkCap();c.scale.setScalar(1.7);addPart(c,'cap',.25,0,-.55,.75);const l=mkLED(0xffc21a,true);l.scale.setScalar(1.8);addPart(l,'led',1.05,0,-.35,.75);
    W(wp(b,-.1,.86,0),wp(s,-.11,.12,0));W(wp(s,.11,.12,0),wp(c,-.03,.02,0));W(wp(c,-.03,.02,0),wp(l,.05,.0,0));W(wp(l,-.025,.0,0),wp(c,.03,.02,0),0x22262c,.3);W(wp(c,.03,.02,0),wp(b,.1,.86,0),0x22262c,.5);R.k=1;},
  steps:[
    {k:'tap',g:'gi',say:'Neste circuito tem uma peça nova, com cara de latinha.',task:'Toque no capacitor',ok:'cap',fb:'Isso! Esse é um capacitor eletrolítico. A faixa clara com sinais de − marca a perna negativa.',hint:'Parece uma latinha azul.',after(){showLabel('cap','Capacitor');}},
    {k:'choose',g:'ar',say:'O capacitor está ligado junto do LED.',task:'O que o capacitor faz?',
     opts:[{t:'Guarda um pouco de energia e solta logo depois',ok:1,fb:'Isso! É como um balde que enche rápido e esvazia rápido. A bateria é que guarda energia por muito tempo.'},{t:'Aumenta a tensão da pilha',fb:'Ele não aumenta a tensão. Ele guarda energia por pouco tempo.'},{t:'Limita a corrente',fb:'Quem limita a corrente é o resistor. O capacitor guarda e solta energia.'}],hint:'Pense num balde pequeno.'},
    {k:'tap',g:'lu',say:'Vamos ver o capacitor trabalhando.',task:'Desligue o interruptor e olhe o LED',ok:'sw',fb:'Viu? O LED não apagou na hora: foi apagando devagar.',hint:'A peça com a alavanquinha.',
     after(){R.sw.userData.set(false);fadeTo(R.led,1,0,3,v=>R.led.userData.set(v));}},
    {k:'choose',g:'al',say:'A pilha já estava desligada, mas o LED continuou aceso por uns segundos.',task:'Por que o LED não apagou na hora?',
     opts:[{t:'O capacitor soltou a energia que tinha guardado',ok:1,fb:'Isso! Quando a pilha saiu, o capacitor "esvaziou o balde" no LED. Fontes de computador usam isso para segurar quedas rápidas de energia.'},{t:'O interruptor está com defeito',fb:'O interruptor desligou certinho. Quem segurou o LED foi o capacitor.'},{t:'O LED guarda luz',fb:'LED não guarda nada. A energia veio do capacitor.'}],hint:'Lembre do balde.'},
    {k:'choose',g:'gi',say:'Cuidado na hora de montar.',task:'O capacitor eletrolítico tem lado certo?',
     opts:[{t:'Sim: a faixa com o sinal − marca a perna negativa',ok:1,fb:'Isso! Ligado ao contrário ele pode estufar e até estourar. A perna mais curta também é a negativa.'},{t:'Não, tanto faz',fb:'O eletrolítico tem polaridade. Ao contrário, ele estraga.'},{t:'Só importa na tomada',fb:'Importa em qualquer circuito: a faixa − sempre vai no negativo.'}],hint:'Olhe a faixa clara na lateral.'}],
  learned:['O capacitor guarda energia por pouco tempo','Ele solta a energia quando a fonte some','Eletrolítico tem polaridade: faixa = −','Fontes usam capacitores contra quedas rápidas']},

el8:{track:'el',n:8,title:'Transistor',
  build(){const b=mkBattery();addPart(b,'bat',-1.2,0,-.45,1.15);const m=mkMotor();m.scale.setScalar(1.5);addPart(m,'motor',.9,0,-.55,.6);
    const t=mkTransistor();t.scale.setScalar(2.4);addPart(t,'tr',0,0,.35,.85);for(const [k,lg] of Object.entries(t.userData.legs)){lg.userData.id=k;R[k]=lg;}
    const s=mkButton(0x4aa8ff);s.scale.setScalar(1.4);addPart(s,'btn',-1.0,0,.85,.4);const lb=label('sinal do Arduino',{size:.11});lb.position.set(-1.0,.42,.85);bench.add(lb);
    W(wp(b,-.1,.86,0),wp(m,-.2,.14,0),0xd23b3b,.4);W(wp(m,.2,.02,.1),wp(t,.045,.0,0),0x22262c,.3);W(wp(t,-.045,0,0),wp(b,.1,.86,0),0x22262c,.5);W(wp(s,0,.12,0),wp(t,0,0,0),0x4aa8ff,.25);R.mspin=0;
    R.updaters.push(dt=>{if(R.mspin)R.motor.userData.prop.rotation.x+=dt*R.mspin;});},
  steps:[
    {k:'tap',g:'al',say:'O motor precisa de bem mais corrente do que um pino do Arduino aguenta. Quem resolve isso é uma peça pequena de 3 pernas.',task:'Toque no transistor',ok:['tr','E','B','C'],fb:'Isso! Esse é o transistor BC548. Ele tem 3 pernas: E, B e C.',hint:'É a peça preta com 3 perninhas.',after(){showLabel('tr','Transistor');}},
    {k:'choose',g:'ar',say:'Pergunta de engenharia.',task:'Por que não ligar o motor direto no pino do Arduino?',
     opts:[{t:'O pino dá pouca corrente, e o motor precisa de muito mais',ok:1,fb:'Isso! Um pino aguenta uns 20 mA. Um motor pequeno puxa 200 mA ou mais, o que estragaria o Arduino.'},{t:'O motor é grande demais',fb:'O problema não é o tamanho, é a corrente: o motor puxa muito mais do que o pino aguenta.'},{t:'Porque o motor é de metal',fb:'O material não importa. O pino do Arduino só aguenta pouca corrente.'}],hint:'Lembre dos mA da Lei de Ohm.'},
    {k:'choose',g:'gi',say:'Então o transistor fica no meio do caminho.',task:'O transistor funciona como…',
     opts:[{t:'Um interruptor controlado por um sinal fraco',ok:1,fb:'Isso! Um sinal pequeno na base (B) libera uma corrente grande entre o coletor (C) e o emissor (E).'},{t:'Uma pilha extra',fb:'Ele não gera energia. A energia vem da bateria; o transistor só abre e fecha o caminho.'},{t:'Um resistor fixo',fb:'Ele é mais esperto: liga e desliga o caminho conforme o sinal na base.'}],hint:'Um sinal fraco controla uma corrente forte.'},
    {k:'tap',g:'lu',say:'O sinal do Arduino entra pela perna do meio, a <b>base</b>.',task:'Toque na perna B do transistor',ok:'B',glow:['E','B','C'],
     wrong:{E:'E é o emissor: por ele a corrente sai para o negativo.',C:'C é o coletor: por ele entra a corrente que vem do motor.',tr:'Toque numa das perninhas, a do meio.'},
     fb:'Isso! Chegou sinal na base e o transistor deixou a corrente passar: o motor girou!',hint:'B fica no meio.',after(){R.mspin=18;}},
    {k:'choose',g:'al',say:'Para fechar.',task:'Sem sinal na base, o motor…',
     opts:[{t:'Fica parado, porque o transistor corta o caminho',ok:1,fb:'Isso! Sem sinal, o transistor fica "desligado". É assim que o Arduino liga e desliga motores, lâmpadas e ventoinhas.'},{t:'Gira mais devagar',fb:'Sem sinal na base, o caminho fica fechado e o motor para.'},{t:'Gira ao contrário',fb:'Para inverter é preciso outro circuito. Sem sinal, ele só para.'}],hint:'Sem sinal = interruptor aberto.',after(){R.mspin=0;}}],
  learned:['Pino do Arduino aguenta pouca corrente','Transistor: interruptor controlado por sinal','B = base, C = coletor, E = emissor','Sinal fraco na base libera corrente forte']},

el9:{track:'el',n:9,title:'Achar o curto',
  build(){const p=mkProto();p.scale.setScalar(1.6);addPart(p,'proto',.25,0,0,.3);const b=mkBattery();b.scale.setScalar(.9);addPart(b,'bat',-1.35,0,-.2,1.05);
    const top=-.5*1.6*.515+.03;const rp=[-.75,.16,-.36],rn=[-.75,.16,-.3];
    W(wp(b,-.1,.86,0),[-.85,.16,-.36],0xd23b3b,.25);W(wp(b,.1,.86,0),[-.85,.16,.42],0x22262c,.3);
    const sh=mkJumper(0xd23b3b,[[-.2,.16,-.37],[-.1,.45,-.1],[0,.45,.2],[.05,.16,.42]]);addPart(sh,'short',0,0,0,.55);sh.userData.ly=.6;
    const w2=mkJumper(0xd23b3b,[[.5,.16,-.37],[.55,.3,-.25],[.6,.16,-.12]]);addPart(w2,'w2',0,0,0,.45);
    const r1=mkResistor(['red','red','brown']);r1.scale.setScalar(1.2);at(r1,.75,.12,-.12);bench.add(r1);
    const l1=mkLED(0xff3b3b);l1.scale.setScalar(1.4);addPart(l1,'led1',.95,.13,.15,.55);const l2=mkLED(0x2fe07a);l2.scale.setScalar(1.4);l2.rotation.y=PI;addPart(l2,'led2',.45,.13,.15,.55);
    const r2=mkResistor(['red','red','brown']);r2.scale.setScalar(1.2);at(r2,.25,.12,-.12);bench.add(r2);
    const hb=halo(0xff4f5e,1.4);hb.position.set(-1.35,.6,-.2);bench.add(hb);R.heat=hb;R.updaters.push((dt,t)=>{if(R.heat.visible)R.heat.material.opacity=.4+.3*Math.sin(t*6);});},
  steps:[
    {k:'info',g:'ar',say:'Esta placa chegou para conserto: a bateria está <b>esquentando</b> e os LEDs não acendem. Há <b>dois defeitos</b>. Vamos achar como técnicas.',task:'Primeiro, sempre: desligue a energia antes de mexer na placa.'},
    {k:'tap',g:'lu',say:'Um curto-circuito é quando o + encontra o − sem passar por nenhuma peça.',task:'Ache o fio que liga o + direto no −',ok:'short',
     wrong:{w2:'Esse fio leva o + até o resistor do LED. Ele está certo.',led1:'O LED não é o curto. Procure um fio que vai da fileira + até a −.',led2:'O LED não é o curto. Procure um fio que vai da fileira + até a −.',proto:'Procure um fio vermelho que atravessa a placa.',bat:'A bateria está esquentando por causa do curto. Procure o fio.'},
     fb:'Isso! Esse fio ia do + direto ao −. Toda a corrente passava por ele, sem passar pelos LEDs, e a bateria esquentava.',hint:'Procure o fio que vai de uma borda até a outra.',after(){lift(R.short,1);R.heat.visible=false;R.led1.userData.set(1);}},
    {k:'tap',g:'gi',say:'Sem o curto, o LED vermelho acendeu. O verde continua apagado.',task:'Ache o LED invertido',ok:'led2',wrong:{led1:'Esse acendeu, então está certo. Compare as perninhas dos dois.'},
     fb:'Isso! A perna comprida dele estava virada para o −. Desvirei e ele acendeu.',hint:'Compare de que lado está a perna mais comprida.',after(){tween(R.led2,{ry:0},.6);setTimeout(()=>R.led2.userData.set(1),600);}},
    {k:'choose',g:'al',say:'Placa consertada!',task:'Por que o curto-circuito é perigoso?',
     opts:[{t:'A corrente fica enorme, esquenta os fios e pode queimar a fonte ou causar fogo',ok:1,fb:'Isso! Sem nenhuma peça segurando, a corrente sobe muito. Por isso a casa tem disjuntores, que desligam sozinhos num curto.'},{t:'Só gasta a pilha mais rápido',fb:'Gasta, mas o pior é o calor: fios e fontes podem queimar.'},{t:'Não é perigoso',fb:'É sim: sem resistência, a corrente fica enorme e esquenta tudo.'}],hint:'Lembre da bateria quente.'}],
  learned:['Curto: + ligado direto no −','Curto esquenta e pode queimar a fonte','LED invertido não acende','Desligue a energia antes de consertar']},

el10:{track:'el',n:10,title:'Lanterna',
  build(){const b=mkBattery();addPart(b,'bat',-1.2,0,-.4,1.15);const bt=mkButton(0xd23b3b);bt.scale.setScalar(1.6);addPart(bt,'btn',-.35,0,.7,.4);
    const r=mkResistor(['orange','orange','brown']);r.scale.setScalar(2);addPart(r,'res',.15,0,-.6,.45);const p=mkPot();p.scale.setScalar(1.6);addPart(p,'pot',.6,0,.55,.6);
    const l=mkLED(0xf4f6ff);l.scale.setScalar(2.2);addPart(l,'led',1.15,0,-.45,.8);l.userData.set(0);
    W(wp(b,-.1,.86,0),wp(bt,0,.08,0));W(wp(bt,0,.08,0),wp(r,-.3,0,0));W(wp(r,.3,0,0),wp(p,0,.02,.14));W(wp(p,.07,.02,.14),wp(l,.05,0,0));W(wp(l,-.025,0,0),wp(b,.1,.86,0),0x22262c,.6);},
  steps:[
    {k:'choose',g:'ar',say:'<b>Desafio final!</b> Vamos montar uma lanterna com tudo que você aprendeu: bateria, botão, resistor, potenciômetro e um LED branco.',task:'Qual peça liga e desliga a lanterna?',
     opts:[{t:'O botão: ele fecha o circuito enquanto está apertado',ok:1,fb:'Isso! Apertou, o caminho fecha. Soltou, abre.'},{t:'O resistor',fb:'O resistor só limita a corrente. Quem liga e desliga é o botão.'},{t:'O LED',fb:'O LED é a luz. Quem abre e fecha o caminho é o botão.'}],hint:'É o que o seu dedo aperta.'},
    {k:'choose',g:'lu',say:'Bateria de 9 V e LED branco, que usa 3 V e 20 mA (0,02 A). Sobram 6 V para o resistor.',task:'Qual resistor usar?',
     opts:[{t:'330 Ω',s:'laranja, laranja, marrom',ok:1,fb:'Isso! A conta dá 6 ÷ 0,02 = 300 Ω. Na loja, o valor mais perto e um pouco acima é 330 Ω, mais seguro para o LED.'},{t:'33 Ω',fb:'Com 33 Ω passariam uns 180 mA, e o LED queimaria.'},{t:'33.000 Ω',fb:'Com 33 kΩ passaria só 0,2 mA, e a lanterna quase não acenderia.'}],hint:'R = 6 ÷ 0,02.'},
    {k:'choose',g:'gi',say:'Agora a ligação.',task:'Como ficam ligados bateria, botão, resistor e LED?',
     opts:[{t:'Em série: um caminho só, passando por todos',ok:1,fb:'Isso! O botão precisa estar no caminho para cortar tudo, e o resistor também, para proteger o LED.'},{t:'Em paralelo',fb:'Em paralelo, o LED acenderia sem passar pelo botão nem pelo resistor.'},{t:'Tanto faz',fb:'Não: se o resistor ficar em paralelo, ele não protege o LED.'}],hint:'O botão precisa cortar o caminho todo.'},
    {k:'tap',g:'al',say:'Tudo montado. Hora de testar.',task:'Aperte o botão',ok:'btn',fb:'A lanterna acendeu! Ainda está fraquinha porque o potenciômetro está no máximo de resistência.',hint:'O botão vermelho.',
     after(){const c=R.btn.userData.cap;tween(c,{y:.08},.15);R.led.userData.set(.35);}},
    {k:'tap',g:'ar',say:'O <b>potenciômetro</b> é um resistor que muda de valor quando você gira.',task:'Gire o potenciômetro para aumentar o brilho',ok:'pot',fb:'Lanterna pronta! Girando, a resistência cai, a corrente sobe e o LED brilha mais. O resistor de 330 Ω continua lá para proteger o LED.',hint:'A peça azul com botão de girar.',
     after(){const k=R.pot.userData.knob;fadeTo(k,0,-2.4,1,v=>{k.rotation.y=v;R.led.userData.set(.35+.65*(v/-2.4));});}}],
  learned:['O botão abre e fecha o circuito','R = V ÷ I, arredondando para cima','Botão, resistor e LED ficam em série','Potenciômetro: resistor que muda de valor']}
});


/* ---------- trilha 4: redes ---------- */
function mkNIC(){const g=new THREE.Group();g.add(at(rbox(.7,.02,.4,.006,0x14532d),0,.02,0));g.add(at(rbox(.18,.03,.18,.004,PLASTIC(0x16191d)),.05,.045,0));
  g.add(at(box(.02,.22,.4,BRUSHED()),-.36,.1,0));g.add(at(rbox(.16,.13,.17,.01,BRUSHED()),-.27,.08,0));g.add(at(box(.4,.012,.05,GOLD()),.05,.008,.2));return g;}
function mkAP(){const g=new THREE.Group();g.add(at(new THREE.Mesh(new THREE.CylinderGeometry(.2,.22,.06,40),PLASTIC(0xf3f1ec,{roughness:.35})),0,.03,0));
  const l=at(new THREE.Mesh(new THREE.TorusGeometry(.12,.01,6,40),mat(0x4aa8ff,{emissive:0x4aa8ff,emissiveIntensity:1.2})),0,.062,0);l.rotation.x=PI/2;g.add(l);return g;}
function mkLock(){const g=new THREE.Group();g.add(at(rbox(.36,.3,.16,.04,mat(0xf5c518,{metalness:.8,roughness:.3})),0,.15,0));
  const sh=new THREE.Mesh(new THREE.TorusGeometry(.12,.03,10,30,PI),METAL());sh.position.y=.3;g.add(sh);const kh=at(cyl(.035,.02,PLASTIC(0x14171b)),0,.17,.081);kh.rotation.x=PI/2;g.add(kh);return g;}
function wifiPath(a,b,h=.6){const A=new THREE.Vector3(...a),B=new THREE.Vector3(...b),M=A.clone().lerp(B,.5);M.y+=h;return new THREE.CatmullRomCurve3([A,M,B]);}
function cable(a,b,col=0x2b62c9,h=.3){const c=netCable(a,b,col,h);bench.add(c);return c;}
Object.assign(NAMES,{modem:'o modem',router:'o roteador',switch:'o switch',cabo:'o cabo de rede',nic:'a placa de rede',notebook:'o notebook',pc:'o computador',phone:'o celular',server:'o servidor',cloud:'a internet',loose:'o cabo solto',
  canto:'o canto do quarto',centro:'o centro da casa',cozinha:'a cozinha',corredor:'o corredor',secretaria:'a secretaria',biblioteca:'a biblioteca',lab2:'o laboratório 2'});
T568B.forEach(([id,nm],i)=>NAMES[id]=`o fio ${nm} (pino ${i+1})`);
function ipTag(o,ip,bad){const l=label(ip,{size:.12,bg:bad?'#c43b4a':'rgba(20,26,34,.92)'});l.position.set(o.position.x,o.position.y+(o.userData.ly||.8),o.position.z);bench.add(l);return l;}

Object.assign(PH,{
rd1:{track:'rd',n:1,title:'As peças da rede',
  build(){addPart(mkModem(),'modem',-1.3,0,-.8,.85);addPart(mkRouter(),'router',.05,0,-1.0,.75);addPart(mkNetSwitch(),'switch',.15,0,.2,.35);
    const cb=new THREE.Group();cb.add(wire([[0,.03,0],[.25,.03,-.2],[.45,.03,0],[.25,.03,.2],[.05,.03,.05],[.3,.06,-.1],[.6,.03,.15]],0x2b62c9,.022));addPart(cb,'cabo',1.0,0,.85,.3);
    addPart(mkNIC(),'nic',1.15,0,-.85,.4);addPart(mkNotebook(),'notebook',-1.2,0,.85,.55);},
  steps:[
    ['modem','o modem','ar','O <b>modem</b> recebe a internet que vem da rua (por fibra ou cabo) e "traduz" para a sua casa.','A caixa branca em pé.'],
    ['router','o roteador','al','O <b>roteador</b> divide a internet entre os aparelhos e cria a rede Wi-Fi. É o "chefe do trânsito" da rede.','A caixa preta com antenas.'],
    ['switch','o switch','lu','O <b>switch</b> tem várias portas para ligar computadores por cabo na mesma rede.','A caixa comprida e prateada, cheia de portas.'],
    ['cabo','o cabo de rede','gi','O <b>cabo de rede</b> (par trançado) leva os dados entre os aparelhos. A ponta dele é o conector RJ45.','O fio azul enrolado.'],
    ['nic','a placa de rede','ar','A <b>placa de rede</b> fica dentro do computador e é onde o cabo se encaixa. Notebooks e celulares têm uma placa Wi-Fi.','Uma plaquinha verde com uma entrada de cabo.'],
    ['notebook','o notebook','al','O <b>notebook</b> é um dos aparelhos que usam a rede, pelo cabo ou pelo Wi-Fi.','O computador portátil aberto.']].map(([id,n,g,fb,hint])=>(
    {k:'tap',g,say:'Toque na peça que eu pedir. Se errar, eu mostro qual é.',task:`Toque n${n.startsWith('a ')?'a':'o'} ${n.slice(2)}`,ok:id,fb,hint,after(){showLabel(id,n.slice(2)[0].toUpperCase()+n.slice(3));}})),
  learned:['Modem: traz a internet da rua','Roteador: divide e cria o Wi-Fi','Switch: liga vários aparelhos por cabo','Cabo de rede com conector RJ45','Placa de rede: a entrada do computador']},

rd2:{track:'rd',n:2,title:'O cabo de rede',
  build(){const r=mkRJ45();r.scale.setScalar(1.35);addPart(r,'rj',0,0,-.1,.8);for(const [k,w] of Object.entries(r.userData.wires)){w.userData.id=k;R[k]=w;}},
  steps:[
    {k:'choose',g:'gi',say:'Este é um conector <b>RJ45</b> gigante e transparente, para ver por dentro.',task:'Quantos fios tem dentro de um cabo de rede comum?',
     opts:[{t:'8 fios, em 4 pares',ok:1,fb:'Isso! São 8 fios coloridos, enrolados de dois em dois.'},{t:'2 fios',fb:'Cabo de energia tem 2. O de rede tem 8, em 4 pares.'},{t:'4 fios',fb:'São 4 pares, mas 8 fios no total.'}],hint:'Conte os fios coloridos.'},
    {k:'choose',g:'ar',say:'Os fios vêm enrolados em pares dentro da capa azul.',task:'Por que os fios são trançados em pares?',
     opts:[{t:'Para diminuir a interferência de um fio no outro',ok:1,fb:'Isso! Trançados, os ruídos elétricos se cancelam. Por isso o nome é "par trançado".'},{t:'Para o cabo ficar mais bonito',fb:'A trança tem função: ela cancela a interferência entre os fios.'},{t:'Para economizar fio',fb:'Trançar até gasta mais fio. O objetivo é diminuir a interferência.'}],hint:'Pense em ruído, como chiado no rádio.'},
    {k:'tap',g:'lu',say:'Para o cabo funcionar, cada fio vai num pino certo. O padrão mais usado é o <b>T568B</b>, que começa com o branco-laranja no pino 1.',task:'Toque no fio do pino 1 (branco-laranja)',ok:'w1',
     wrong:Object.fromEntries(T568B.slice(1).map(([id,nm],i)=>[id,`Esse é o ${nm}, do pino ${i+2}. O pino 1 é o branco-laranja, na ponta.`])),fb:'Isso! Pino 1: branco-laranja. Pino 2: laranja. A ordem é sempre a mesma nas duas pontas.',hint:'Branco com listras laranja, na ponta.'},
    {k:'tap',g:'al',say:'Uma curiosidade: o par azul fica no meio do conector, separado do resto.',task:'Toque no fio azul',ok:'w4',
     wrong:Object.fromEntries(T568B.filter(x=>x[0]!=='w4').map(([id,nm])=>[id,`Esse é o ${nm}. O azul liso fica no meio, no pino 4.`])),fb:'Isso! O azul fica no pino 4 e o branco-azul no 5, bem no meio.',hint:'Azul liso, sem listras.'},
    {k:'choose',g:'gi',say:'Fim da aula do cabo.',task:'E se as cores estiverem em ordem diferente nas duas pontas?',
     opts:[{t:'O cabo pode não funcionar ou ficar lento',ok:1,fb:'Isso! As duas pontas precisam seguir o mesmo padrão. Técnicos usam um testador de cabo para conferir.'},{t:'Funciona igual',fb:'Se os pares trocarem de lugar, os dados chegam errados ou não chegam.'},{t:'Fica mais rápido',fb:'Trocar a ordem nunca deixa mais rápido. O cabo pode até parar.'}],hint:'Os dois lados precisam combinar.'}],
  learned:['Cabo de rede: 8 fios em 4 pares trançados','A trança diminui a interferência','Padrão T568B: pino 1 branco-laranja','As duas pontas precisam seguir o mesmo padrão']},

rd3:{track:'rd',n:3,title:'Rede de casa',
  build(){const m=mkModem();addPart(m,'modem',-1.25,0,-.85,.85);const r=mkRouter();addPart(r,'router',.15,0,-.95,.75);const pc=mkPC();pc.scale.setScalar(.8);addPart(pc,'pc',.9,0,.55,.7);
    const ph=mkPhone();ph.scale.setScalar(1.3);addPart(ph,'phone',-.8,0,.75,.5);
    const f=wire([[-2.2,.02,-1.3],[-1.8,.05,-1.0],[-1.45,.12,-.85]],0xf08a24,.018);bench.add(f);R.fiber=addFlow(f.userData.curve,0xf08a24,3,.35);},
  steps:[
    {k:'tap',g:'ar',say:'Vamos montar a rede de uma casa. O fio laranja é a fibra óptica que vem da rua.',task:'Toque no aparelho onde a internet da rua chega primeiro',ok:'modem',wrong:{router:'O roteador recebe a internet do modem. Siga o fio laranja que vem da rua.',pc:'O PC é o último da fila. Siga o fio laranja.',phone:'O celular usa a internet, mas ela chega primeiro em outro aparelho.'},
     fb:'Isso! A fibra chega no modem.',hint:'Siga o fio laranja.'},
    {k:'tap',g:'al',say:'Agora o modem precisa entregar a internet para quem vai dividir.',task:'Ligue o cabo do modem no roteador: toque no roteador',ok:'router',fb:'Isso! Cabo do modem na porta WAN (de internet) do roteador.',hint:'A caixa preta com antenas.',
     after(){const c=cable([-1.25,.12,-.62],[.15,.08,-1.2],0x2b62c9,.35);R.c1=addFlow(c.userData.curve,0x4aa8ff,3,.4);}},
    {k:'tap',g:'lu',say:'O computador fica perto e precisa de conexão firme.',task:'Ligue o PC por cabo: toque no PC',ok:'pc',fb:'Isso! Cabo do roteador até a placa de rede do PC.',hint:'O computador com monitor.',
     after(){const c=cable([.15,.08,-.72],[.55,.12,.45],0x2b62c9,.3);R.c2=addFlow(c.userData.curve,0x4aa8ff,3,.4);}},
    {k:'choose',g:'gi',say:'O celular não tem entrada de cabo de rede.',task:'Como o celular entra na rede?',
     opts:[{t:'Pelo Wi-Fi do roteador, sem cabo',ok:1,fb:'Isso! O roteador manda os dados por ondas de rádio. As bolinhas pelo ar mostram isso.'},{t:'Pelo cabo do carregador',fb:'O carregador só dá energia. A rede chega pelo Wi-Fi.'},{t:'Direto pela fibra',fb:'A fibra chega só no modem. O celular usa o Wi-Fi do roteador.'}],hint:'Sem fio = wireless = Wi-Fi.',
     after(){R.wf=wifiRings(new THREE.Vector3(.15,.5,-.95));addFlow(wifiPath([.15,.5,-.95],[-.8,.4,.75]),0x36d399,3,.4);}},
    {k:'choose',g:'ar',say:'Rede de casa pronta!',task:'Qual é a diferença entre modem e roteador?',
     opts:[{t:'O modem traz a internet; o roteador divide entre os aparelhos e cria o Wi-Fi',ok:1,fb:'Isso! Muitas operadoras entregam os dois num aparelho só, mas as funções continuam separadas.'},{t:'São a mesma coisa',fb:'Às vezes vêm na mesma caixa, mas fazem coisas diferentes.'},{t:'O roteador traz a internet e o modem cria o Wi-Fi',fb:'É o contrário: modem traz, roteador divide.'}],hint:'Quem recebeu a fibra?'}],
  learned:['A internet chega no modem','O roteador divide a internet','Aparelhos perto podem usar cabo','O celular entra pelo Wi-Fi']},

rd4:{track:'rd',n:4,title:'Endereço IP',
  build(){const r=mkRouter();addPart(r,'router',0,0,-1.0,.75);const pc=mkPC();pc.scale.setScalar(.7);addPart(pc,'pc',-1.05,0,.45,.75);
    const nb=mkNotebook();addPart(nb,'notebook',.05,0,.75,.55);const ph=mkPhone();ph.scale.setScalar(1.3);addPart(ph,'phone',1.15,0,.5,.55);
    const c=cable([0,.08,-.77],[-1.35,.12,.25],0x2b62c9,.3);addFlow(c.userData.curve,0x4aa8ff,2,.35);wifiRings(new THREE.Vector3(0,.5,-1.0));
    ipTag(R.router,'192.168.0.1');ipTag(R.pc,'192.168.0.10');ipTag(R.notebook,'192.168.0.11');R.ipPh=ipTag(R.phone,'192.168.0.10',true);},
  steps:[
    {k:'choose',g:'lu',say:'Cada aparelho da rede tem um número, como <b>192.168.0.10</b>.',task:'O que é o endereço IP?',
     opts:[{t:'O endereço de cada aparelho na rede',ok:1,fb:'Isso! É como o número da casa: os dados sabem para onde ir.'},{t:'A senha do Wi-Fi',fb:'A senha protege a rede. O IP é o endereço de cada aparelho.'},{t:'A velocidade da internet',fb:'A velocidade é outra coisa. O IP é o endereço do aparelho.'}],hint:'Pense no CEP e no número da casa.'},
    {k:'choose',g:'ar',say:'Ninguém digitou esses números à mão.',task:'Quem distribui os IPs numa rede de casa?',
     opts:[{t:'O roteador, automaticamente',ok:1,fb:'Isso! O roteador tem um serviço chamado DHCP, que entrega um IP livre para cada aparelho que entra.'},{t:'A operadora, por telefone',fb:'A operadora dá o IP da casa na internet. Dentro de casa, quem distribui é o roteador.'},{t:'Cada aparelho escolhe o seu',fb:'Se cada um escolhesse, haveria IP repetido. O roteador organiza isso.'}],hint:'O chefe do trânsito da rede.'},
    {k:'tap',g:'gi',say:'Ops! A etiqueta vermelha mostra um <b>conflito</b>: dois aparelhos com o mesmo IP. O celular foi o último a entrar.',task:'Toque no aparelho que precisa trocar de IP',ok:'phone',
     wrong:{pc:'O PC tem esse IP, mas chegou antes. Quem precisa trocar é o celular, que chegou depois.',notebook:'O notebook tem o .11, que é único.',router:'O roteador é o .1, sem conflito.'},
     fb:'Isso! O roteador deu um IP novo para o celular: 192.168.0.12. Conflito resolvido.',hint:'Procure a etiqueta vermelha.',after(){bench.remove(R.ipPh);ipTag(R.phone,'192.168.0.12');}},
    {k:'choose',g:'al',say:'Dica de técnica.',task:'O endereço 192.168.0.1 quase sempre é…',
     opts:[{t:'O próprio roteador',ok:1,fb:'Isso! Digitando esse endereço no navegador, você abre o painel de configuração do roteador.'},{t:'Um site da internet',fb:'Endereços 192.168 são só da rede interna. O .1 costuma ser o roteador.'},{t:'O celular',fb:'O celular ganhou o .12. O .1 é o roteador.'}],hint:'Olhe a etiqueta da caixa preta.'}],
  learned:['IP: o endereço de cada aparelho','O roteador distribui os IPs (DHCP)','IP repetido causa conflito','192.168.0.1 costuma ser o roteador']},

rd5:{track:'rd',n:5,title:'Wi-Fi',
  build(){bench.add(mkHouse());[['canto',-1.35,-1.35],['centro',.05,.35],['cozinha',1.25,-1.05]].forEach(([id,x,z])=>{const s=spot(id,x,z);bench.add(s);R[id]=s;});
    const r=mkRouter();r.scale.setScalar(.55);r.visible=false;bench.add(r);R.router=r;},
  steps:[
    {k:'tap',g:'al',say:'Planta de uma casa vista de cima. Vamos escolher o lugar do roteador.',task:'Toque no melhor lugar para o roteador',ok:'centro',glow:['canto','centro','cozinha'],
     wrong:{canto:'No canto da casa, o sinal gasta força atravessando paredes e chega fraco do outro lado.',cozinha:'Perto do micro-ondas o Wi-Fi sofre interferência: os dois usam a mesma faixa, de 2,4 GHz.'},
     fb:'Isso! No centro, o sinal se espalha por igual para todos os cômodos.',hint:'Pense num lugar de onde todos os cômodos fiquem perto.',
     after(){const r=R.router;r.visible=true;r.position.set(.05,.4,.35);const d=new THREE.Mesh(new THREE.CircleGeometry(1.7,64),new THREE.MeshBasicMaterial({color:0x4aa8ff,transparent:true,opacity:.13,depthWrite:false}));d.rotation.x=-PI/2;d.position.set(.05,.06,.35);bench.add(d);wifiRings(new THREE.Vector3(.05,.5,.35));}},
    {k:'choose',g:'lu',say:'O Wi-Fi são ondas de rádio, e algumas coisas atrapalham.',task:'O que mais atrapalha o sinal do Wi-Fi?',
     opts:[{t:'Paredes grossas, espelhos, metal e o micro-ondas',ok:1,fb:'Isso! Concreto e metal bloqueiam, espelhos refletem e o micro-ondas faz interferência.'},{t:'Cortinas e almofadas',fb:'Tecido quase não atrapalha. Os vilões são paredes, metal, espelhos e o micro-ondas.'},{t:'A luz do sol',fb:'A luz não atrapalha o Wi-Fi. Paredes e metal sim.'}],hint:'Pense em coisas pesadas e metálicas.'},
    {k:'choose',g:'gi',say:'Roteadores novos têm duas redes: 2,4 GHz e 5 GHz.',task:'Qual a diferença entre elas?',
     opts:[{t:'5 GHz é mais rápida, mas alcança menos e atravessa menos paredes',ok:1,fb:'Isso! Perto do roteador, use 5 GHz. Longe, a de 2,4 GHz chega melhor.'},{t:'2,4 GHz é sempre melhor',fb:'Ela alcança mais longe, mas é mais lenta e mais disputada.'},{t:'São iguais',fb:'Não: 5 GHz é mais rápida e 2,4 GHz alcança mais longe.'}],hint:'Rápida × longe.'},
    {k:'choose',g:'ar',say:'Último ajuste.',task:'Por que é melhor deixar o roteador num lugar alto?',
     opts:[{t:'O sinal se espalha melhor, sem móveis no caminho',ok:1,fb:'Isso! No chão ou dentro de armário, móveis e paredes absorvem o sinal.'},{t:'Para ninguém mexer',fb:'Ajuda, mas o principal é o sinal: no alto ele passa por cima dos móveis.'},{t:'Não faz diferença',fb:'Faz diferença: no chão, o sinal bate nos móveis.'}],hint:'Ondas se espalham para todos os lados.'}],
  learned:['Roteador no centro da casa','Paredes, metal, espelhos e micro-ondas atrapalham','5 GHz: rápida; 2,4 GHz: alcança mais','Roteador no alto, fora de armários']},

rd6:{track:'rd',n:6,title:'Switch',
  build(){const r=mkRouter();r.scale.setScalar(.8);addPart(r,'router',-1.15,0,-1.05,.65);addPart(mkNetSwitch(),'switch',.1,0,-.25,.35);
    R.pcs=[];[-1.25,-.42,.42,1.25].forEach((x,i)=>{const p=mkPC();p.scale.setScalar(.5);at(p,x,0,.85);p.userData.id='pc';bench.add(p);R.pcs.push(p);});R.pc=R.pcs[0];},
  steps:[
    {k:'tap',g:'gi',say:'Um laboratório com 4 computadores e um roteador com poucas portas.',task:'Toque no switch',ok:'switch',fb:'Isso! O switch tem 8 portas para ligar vários aparelhos por cabo.',hint:'A caixa prateada comprida.',after(){showLabel('switch','Switch');}},
    {k:'choose',g:'ar',say:'Por que não ligar tudo no roteador?',task:'Para que serve o switch?',
     opts:[{t:'Ligar vários aparelhos por cabo na mesma rede',ok:1,fb:'Isso! Ele multiplica as portas e entrega cada dado só para o aparelho certo.'},{t:'Trazer a internet da rua',fb:'Quem traz a internet é o modem. O switch multiplica as portas da rede.'},{t:'Criar o Wi-Fi',fb:'Wi-Fi é com o roteador ou com pontos de acesso. O switch é só para cabos.'}],hint:'Pense em uma régua de tomadas, só que para rede.'},
    {k:'tap',g:'lu',say:'Primeiro, o switch precisa estar ligado na rede.',task:'Ligue o switch no roteador: toque no roteador',ok:'router',fb:'Isso! Agora o switch faz parte da rede.',hint:'A caixa preta com antenas.',
     after(){const c=cable([-1.15,.07,-.86],[-.3,.05,-.08],0x2b62c9,.3);addFlow(c.userData.curve,0x4aa8ff,3,.4);}},
    {k:'tap',g:'al',say:'Agora os computadores.',task:'Toque no switch para ligar os 4 PCs',ok:'switch',fb:'Isso! Cada PC num cabo, todos na mesma rede. As bolinhas mostram os dados indo só para o PC certo.',hint:'A caixa prateada.',
     after(){R.pcs.forEach((p,i)=>{const c=cable([-.25+i*.17,.05,-.07],[p.position.x-.21,.08,.72],0x2b62c9,.25);addFlow(c.userData.curve,0x4aa8ff,2,.45,i%2);});}},
    {k:'choose',g:'gi',say:'Laboratório ligado!',task:'Qual a diferença entre switch e roteador?',
     opts:[{t:'O switch liga aparelhos na mesma rede; o roteador liga a rede à internet',ok:1,fb:'Isso! Numa escola, vários switches ficam ligados a um roteador principal.'},{t:'São iguais',fb:'O roteador conversa com a internet e distribui IPs. O switch só multiplica portas.'},{t:'O switch é mais rápido para a internet',fb:'A velocidade da internet depende do plano e do roteador. O switch organiza a rede interna.'}],hint:'Quem conversa com a internet?'}],
  learned:['Switch: muitas portas na mesma rede','O switch é ligado no roteador','Cada PC usa um cabo até o switch','O roteador liga a rede à internet']},

rd7:{track:'rd',n:7,title:'Caminho do dado',
  build(){const pc=mkPC();pc.scale.setScalar(.6);addPart(pc,'pc',-1.25,0,.75,.6);const r=mkRouter();r.scale.setScalar(.7);addPart(r,'router',-.55,0,-.15,.6);
    const m=mkModem();m.scale.setScalar(.8);addPart(m,'modem',.15,0,-1.0,.7);const cl=mkCloud();cl.scale.setScalar(.9);addPart(cl,'cloud',1.05,1.0,-1.1,.55);const s=mkServer();s.scale.setScalar(.75);addPart(s,'server',1.3,0,.55,.85);
    R.path=[cable([-1.5,.08,.6],[-.55,.06,.0],0x2b62c9,.25),cable([-.55,.06,-.32],[.0,.1,-1.0],0x2b62c9,.3),cable([.25,.3,-1.0],[.85,.95,-1.1],0xf08a24,.2),cable([1.25,.95,-1.0],[1.3,.4,.35],0xf08a24,.2)];},
  steps:[
    {k:'choose',g:'ar',say:'Você digitou o nome de um site no PC. Os dados precisam chegar até o computador onde o site está guardado.',task:'Qual é o caminho?',
     opts:[{t:'PC → roteador → modem → internet → servidor do site',ok:1,fb:'Isso! E a resposta faz o caminho de volta.'},{t:'PC → servidor, direto',fb:'O PC não alcança o servidor sozinho: passa pelo roteador, pelo modem e pela internet.'},{t:'PC → modem → PC',fb:'Os dados precisam sair de casa, cruzar a internet e chegar no servidor.'}],hint:'Siga os cabos.',after(){R.path.forEach(c=>addFlow(c.userData.curve,0x4aa8ff,2,.5));}},
    {k:'tap',g:'lu',say:'O site não fica "na internet" solto: ele fica guardado num computador ligado o tempo todo.',task:'Toque no servidor onde o site está guardado',ok:'server',fb:'Isso! O servidor fica num datacenter e responde a milhares de pedidos ao mesmo tempo.',hint:'O gabinete alto com luzinhas.'},
    {k:'choose',g:'gi',say:'Você digitou um nome, como desmontar.com.br, mas a rede só entende números (IP).',task:'Quem transforma o nome do site no IP do servidor?',
     opts:[{t:'O DNS, uma espécie de agenda da internet',ok:1,fb:'Isso! O DNS recebe o nome e devolve o IP do servidor, como uma agenda de contatos.'},{t:'O switch',fb:'O switch só liga aparelhos por cabo. Quem traduz nomes é o DNS.'},{t:'O próprio PC adivinha',fb:'O PC pergunta para um servidor de DNS.'}],hint:'Nome → número, como uma agenda.'},
    {k:'choose',g:'al',say:'Uma página tem textos, fotos e vídeos.',task:'Como os dados viajam pela rede?',
     opts:[{t:'Em pacotes pequenos, que são juntados de novo no fim',ok:1,fb:'Isso! Cada bolinha é um pacote. Se um se perde, só ele é mandado de novo.'},{t:'Num bloco único e gigante',fb:'Seria lento e frágil. A rede corta tudo em pacotes pequenos.'},{t:'Letra por letra',fb:'É mais eficiente que isso: pacotes com muitos dados cada.'}],hint:'Olhe as bolinhas nos cabos.',after(){R.path.forEach(c=>addFlow(c.userData.curve,0x36d399,2,.5,true));}}],
  learned:['PC → roteador → modem → internet → servidor','Sites ficam em servidores','DNS: transforma nome em IP','Os dados viajam em pacotes']},

rd8:{track:'rd',n:8,title:'Sem internet',
  build(){const m=mkModem();addPart(m,'modem',-1.25,0,-.85,.85);const r=mkRouter();addPart(r,'router',.15,0,-.95,.75);const pc=mkPC();pc.scale.setScalar(.8);addPart(pc,'pc',.95,0,.6,.7);
    const ph=mkPhone();ph.scale.setScalar(1.3);addPart(ph,'phone',-.85,0,.8,.5);const c=cable([-1.25,.12,-.62],[.15,.08,-1.2]);addFlow(c.userData.curve,0x4aa8ff,3,.4);wifiRings(new THREE.Vector3(.15,.5,-.95));
    const lc=new THREE.Group();lc.add(wire([[.15,.08,-.72],[.25,.2,-.4],[.35,.02,-.1],[.5,.02,.05]],0x2b62c9,.022));lc.add(at(rbox(.06,.05,.09,.01,mat(0xffffff,{transparent:true,opacity:.6})),.5,.03,.05));addPart(lc,'loose',0,0,0,.4);
    const x=label('sem internet',{size:.13,bg:'#c43b4a'});x.position.set(.95,1.0,.6);bench.add(x);R.noNet=x;},
  steps:[
    {k:'info',g:'al',say:'Chamado de suporte: "<b>O computador está sem internet!</b>" O celular, no Wi-Fi, funciona.',task:'Vamos investigar como técnicas, do mais simples para o mais difícil.'},
    {k:'choose',g:'ar',say:'Antes de mexer em configuração…',task:'Qual o primeiro passo?',
     opts:[{t:'Olhar as luzes e os cabos do modem, do roteador e do PC',ok:1,fb:'Isso! A maioria dos problemas é cabo solto ou aparelho desligado.'},{t:'Formatar o computador',fb:'Seria o último recurso, e quase nunca resolve problema de rede.'},{t:'Trocar de operadora',fb:'O celular funciona, então a internet está chegando. O problema é aqui dentro.'}],hint:'Comece pelo mais simples.'},
    {k:'tap',g:'lu',say:'Olhe com atenção os cabos.',task:'Ache o cabo solto',ok:'loose',fb:'Achou! O cabo do PC estava fora da porta. Encaixei de novo, até o clique.',hint:'Um dos cabos termina na mesa, sem chegar em nada.',
     after(){bench.remove(R.loose);bench.remove(R.noNet);const c=cable([.15,.08,-.72],[.6,.12,.5]);addFlow(c.userData.curve,0x4aa8ff,3,.4);}},
    {k:'choose',g:'gi',say:'Outro chamado: o PC por cabo funciona, mas o celular não conecta no Wi-Fi.',task:'Onde está o problema?',
     opts:[{t:'No Wi-Fi: reconectar o celular ou reiniciar o roteador',ok:1,fb:'Isso! Se o cabo funciona, a internet chega. O problema está só na parte sem fio.'},{t:'No modem',fb:'Se o PC navega, o modem está ok. O problema é o Wi-Fi.'},{t:'No cabo do PC',fb:'O PC está funcionando. O problema é só no Wi-Fi.'}],hint:'O que funciona e o que não funciona?'},
    {k:'choose',g:'al',say:'Clássico do suporte.',task:'Por que reiniciar o roteador resolve tantos problemas?',
     opts:[{t:'Ele limpa a memória e refaz as conexões do zero',ok:1,fb:'Isso! Depois de dias ligado, o roteador pode acumular erros. Reiniciado, ele começa limpo.'},{t:'Ele baixa uma internet nova',fb:'A internet é a mesma. Reiniciar só limpa a memória e refaz as conexões.'},{t:'Não resolve nada',fb:'Resolve muitas vezes, porque limpa erros acumulados.'}],hint:'Pense em reiniciar o celular.'}],
  learned:['Comece pelas luzes e cabos','Cabo solto é o problema mais comum','Cabo funciona e Wi-Fi não = problema no Wi-Fi','Reiniciar limpa erros acumulados']},

rd9:{track:'rd',n:9,title:'Rede segura',
  build(){const r=mkRouter();addPart(r,'router',-.45,0,-.6,.75);const l=mkLock();l.scale.setScalar(1.4);addPart(l,'lock',.85,0,-.75,.65);
    const ph=mkPhone();ph.scale.setScalar(1.3);addPart(ph,'phone',-1.2,0,.7,.5);const nb=mkNotebook();addPart(nb,'notebook',.6,0,.75,.55);wifiRings(new THREE.Vector3(-.45,.5,-.6),0x36d399);},
  steps:[
    {k:'choose',g:'gi',say:'Uma rede aberta deixa qualquer pessoa entrar e até espiar o que passa nela.',task:'Qual é a senha de Wi-Fi mais segura?',
     opts:[{t:'Uma frase longa com números e símbolos, como Gato#Azul#Pula7',ok:1,fb:'Isso! Senhas longas demoram anos para serem descobertas, mesmo por computadores.'},{t:'12345678',fb:'É uma das senhas mais usadas do mundo: descoberta em segundos.'},{t:'O nome da família',fb:'Fácil de adivinhar para quem conhece vocês.'}],hint:'Tamanho importa.'},
    {k:'choose',g:'ar',say:'Visitas sempre pedem a senha do Wi-Fi.',task:'Para que serve a rede de visitantes?',
     opts:[{t:'Dar internet às visitas sem acesso aos aparelhos da casa',ok:1,fb:'Isso! A rede de visitantes fica separada: navega, mas não enxerga computadores, impressoras e câmeras.'},{t:'Deixar a internet mais rápida',fb:'Ela não acelera nada. Ela separa as visitas dos seus aparelhos.'},{t:'Bloquear as visitas',fb:'Ela libera a internet, só que isolada.'}],hint:'Separar.'},
    {k:'choose',g:'lu',say:'O cadeado da mesa representa uma proteção do roteador.',task:'O que o firewall faz?',
     opts:[{t:'Bloqueia conexões suspeitas que tentam entrar na rede',ok:1,fb:'Isso! O firewall é como um porteiro: deixa passar o que é permitido e barra o resto.'},{t:'Apaga vírus do computador',fb:'Quem apaga vírus é o antivírus. O firewall barra conexões.'},{t:'Aumenta o sinal do Wi-Fi',fb:'Não mexe no sinal. Ele controla o que entra e o que sai da rede.'}],hint:'Um porteiro.'},
    {k:'choose',g:'al',say:'Muitos roteadores saem de fábrica com o painel acessado por admin/admin.',task:'O que fazer ao instalar um roteador novo?',
     opts:[{t:'Trocar a senha do painel de configuração',ok:1,fb:'Isso! Com a senha de fábrica, qualquer pessoa na rede pode mudar tudo no roteador.'},{t:'Deixar como veio',fb:'A senha de fábrica é pública na internet. Troque sempre.'},{t:'Desligar o Wi-Fi para sempre',fb:'Não precisa. Trocar a senha do painel já protege muito.'}],hint:'Senha de fábrica = senha conhecida.'},
    {k:'choose',g:'gi',say:'Última configuração.',task:'Qual proteção escolher para o Wi-Fi?',
     opts:[{t:'WPA2 ou WPA3',ok:1,fb:'Isso! Elas embaralham os dados no ar. WPA3 é a mais nova e mais forte.'},{t:'Rede aberta, sem senha',fb:'Qualquer pessoa entra e pode espiar os dados.'},{t:'WEP',fb:'O WEP é antigo e pode ser quebrado em minutos.'}],hint:'A mais nova.',after(){R.lock.rotation.y=0;tween(R.lock,{y:.15},.3);}}],
  learned:['Senha longa com números e símbolos','Rede de visitantes separada','Firewall barra conexões suspeitas','Troque a senha de fábrica do roteador','Use WPA2 ou WPA3']},

rd10:{track:'rd',n:10,title:'Rede da escola',
  build(){bench.add(mkSchool());const m=mkModem();m.scale.setScalar(.45);at(m,-1.45,.04,1.3);bench.add(m);const r=mkRouter();r.scale.setScalar(.5);addPart(r,'router',-1.0,.04,1.25,.45);
    const sw=mkNetSwitch();sw.scale.setScalar(.5);addPart(sw,'switch',-1.0,.04,-.55,.3);
    [['corredor',.0,0],['secretaria',-.55,.75],['biblioteca',1.15,.75]].forEach(([id,x,z])=>{const s=spot(id,x,z,0x4aa8ff);bench.add(s);R[id]=s;});},
  steps:[
    {k:'choose',g:'ar',say:'<b>Desafio final!</b> Uma escola pequena: 2 laboratórios, secretaria e biblioteca. O roteador fica na secretaria.',task:'O Laboratório 1 tem 8 PCs. O que ele precisa?',
     opts:[{t:'Um switch, para ligar todos os PCs por cabo',ok:1,fb:'Isso! O switch do laboratório recebe um cabo do roteador e distribui para os PCs.'},{t:'Um modem para cada PC',fb:'Um modem só basta. Dentro da escola, quem distribui é o switch.'},{t:'Nada, o Wi-Fi resolve',fb:'Para 8 PCs fixos, o cabo é mais estável e rápido.'}],hint:'Lembre da fase VI.'},
    {k:'tap',g:'lu',say:'Os alunos também usam celular e notebook.',task:'Onde colocar o ponto de acesso Wi-Fi para cobrir a escola?',ok:'corredor',glow:['corredor','secretaria','biblioteca'],
     wrong:{secretaria:'Na secretaria, o sinal fica preso no canto da escola e não chega bem aos laboratórios.',biblioteca:'Na biblioteca, os laboratórios ficariam longe e atrás de várias paredes.'},
     fb:'Isso! No corredor, no meio da escola, o sinal chega em todas as salas.',hint:'O lugar mais central.',after(){const a=mkAP();at(a,0,.32,0);bench.add(a);wifiRings(new THREE.Vector3(0,.4,0));}},
    {k:'choose',g:'gi',say:'Alunos e secretaria na mesma rede?',task:'Como organizar as redes da escola?',
     opts:[{t:'Separar: uma rede para alunos e outra para a secretaria',ok:1,fb:'Isso! A secretaria tem notas e dados pessoais. Alunos navegam numa rede separada, sem enxergar esses computadores.'},{t:'Tudo junto, com a mesma senha',fb:'Assim qualquer aluno poderia acessar os computadores da secretaria.'},{t:'Sem senha, para ficar fácil',fb:'Rede aberta numa escola é um risco grande.'}],hint:'Lembre da rede de visitantes.'},
    {k:'tap',g:'al',say:'Falta ligar o laboratório na rede.',task:'Toque no switch do Laboratório 1 para ligar ao roteador',ok:'switch',fb:'Isso! Cabo do roteador até o switch, e do switch para cada PC.',hint:'A caixinha prateada no Laboratório 1.',
     after(){const c=cable([-1.0,.1,1.15],[-1.0,.1,-.45],0x2b62c9,.35);addFlow(c.userData.curve,0x4aa8ff,4,.35);}},
    {k:'choose',g:'ar',say:'A escola vai ganhar um prédio novo, a 150 metros.',task:'Como levar a rede até lá?',
     opts:[{t:'Com fibra óptica, porque o cabo de rede comum vai só até 100 m',ok:1,fb:'Isso! Depois de 100 m o sinal do cabo de cobre enfraquece. A fibra leva luz por quilômetros.'},{t:'Com um cabo de rede comum bem comprido',fb:'O cabo comum funciona bem só até 100 m. Para 150 m, use fibra.'},{t:'Com várias extensões de tomada',fb:'Extensão leva energia, não rede.'}],hint:'Lembre da fibra que chega no modem.'}],
  learned:['Switch para cada laboratório','Ponto de acesso no centro','Redes separadas para alunos e secretaria','Cabo comum até 100 m; depois, fibra']}
});


/* ---------- 4ª alternativa de cada pergunta: errada, mas plausível ---------- */
const EXTRA={
'zero:1':['Para a câmera medir a luz da sala e ajustar o brilho dos objetos','O brilho é ajustado pela própria câmera. O marcador serve para achar os 4 cantos e ler o desenho.'],
'zero:3':['Para saber a que distância a mesa está do chão','A altura da mesa não importa. O tamanho conhecido serve para desenhar os objetos na escala certa.'],
'zero:4':['O objeto fica parado no último lugar em que a câmera viu o marcador','Alguns apps tentam isso por um instante, mas aqui, sem o marcador, a RA não sabe onde desenhar e o objeto some.'],
'hw2:0':['Processador com soquete S5 ou S6, porque os mais novos sempre servem','Soquete diferente não encaixa, mesmo sendo mais novo. Tem que ser exatamente S5.'],
'hw2:2':['Encaixar primeiro um canto e depois empurrar os outros três','Encaixar torto entorta os contatos. Com os triângulos alinhados, ele desce reto e cai no lugar.'],
'hw2:3':['Espalhar com o dedo uma camada fina antes de colocar o processador','A gordura do dedo e o pó atrapalham. Basta uma gota: o cooler espalha sozinho.'],
'hw3:0':['O pente com mais memória, de qualquer geração','A quantidade de memória não importa se a geração estiver errada: só DDR5 encaixa nessa placa.'],
'hw3:3':['Para o PC reconhecer os dois pentes, porque no mesmo canal só um funciona','No mesmo canal os dois funcionam, só que se revezam. Em canais diferentes eles trabalham juntos e a memória fica mais rápida.'],
'hw3:4':['A luz colorida do pente acende assim que ele encaixa','A luz só acende com o PC ligado. Antes disso, o sinal é a trava das pontas fechando com um clique.'],
'rb2:0':['É o lado que vai no GND, porque o negativo precisa de mais metal','O GND recebe a perna menor. A perna maior é o positivo (+).'],
'rb2:1':['10 Ω, porque resistor pequeno deixa o LED mais forte','10 Ω segura pouco: passa corrente demais e o LED pode queimar. 220 Ω é o valor seguro.'],
'rb3:0':['Verde → amarelo → vermelho → amarelo → verde','No Brasil o amarelo aparece só antes do vermelho. Depois do vermelho volta direto o verde.'],
'rb3:1':['Os três ficam acesos pelo mesmo tempo','Verde e vermelho duram mais. O amarelo é só um aviso, por isso dura pouco.'],
'rb3:4':['O amarelo fica aceso o tempo todo','Sem o fio, nenhuma corrente chega no LED amarelo: ele fica apagado, não aceso.'],
'el1:0':['A lâmpada está ligada ao contrário','Lâmpada comum funciona nos dois sentidos. O problema é o fio solto, que deixa o caminho aberto.'],
'el1:2':['Sai do − da pilha, vai até a lâmpada e para lá','A corrente não para na lâmpada: ela passa e volta para a pilha, fechando o circuito.'],
'el1:3':['A lâmpada acende, mas o barbante esquenta','O barbante nem deixa a corrente passar, então nada esquenta: a lâmpada apaga.'],
'el2:0':['Mostrar quais furos estão quebrados','As linhas não marcam defeito: vermelha é o + e azul é o −, para levar energia à placa toda.'],
'el2:2':['Separar os componentes de 5 V dos de 3,3 V','A tensão é você quem escolhe na ligação. O canal existe para encaixar chips com uma fileira de pernas de cada lado.'],
'el2:3':['Ele acende, mas pisca sem parar','Na mesma coluna as pernas ficam em curto: a corrente desvia e o LED fica apagado.'],
'el3:0':['Para aumentar a tensão que chega no LED','Ele faz o contrário: segura a corrente. Nenhum resistor aumenta a tensão.'],
'el3:2':['10 Ω, porque o vermelho vale 2 zeros a menos','O vermelho, na 3ª faixa, acrescenta 2 zeros: 10 com 2 zeros = 1.000 Ω.'],
'el3:3':['Ele acende mais fraco, porque falta o resistor','Sem resistor ele acende forte demais, esquenta e queima.'],
'el3:4':['Mostra que o resistor aguenta mais calor','A potência que ele aguenta vem do tamanho. A faixa dourada é a margem de erro (5%).'],
'el4:1':['As lâmpadas em série são de outro modelo','As lâmpadas são iguais. O que muda é que os 9 V se dividem entre as duas.'],
'el4:2':['Só a queimada apaga, porque cada uma tem seu fio','Isso acontece no paralelo. Em série o caminho é um só, então as duas apagam.'],
'el4:3':['Em série, para economizar fio','Em série, uma lâmpada queimada apagaria a casa toda. Por isso a instalação é em paralelo.'],
'el5:1':['0,2 A, ou seja, 200 mA','Confira as casas decimais: 9 ÷ 450 = 0,02 A = 20 mA.'],
'el5:2':['330 Ω, porque é o valor de loja mais comum','330 Ω funciona, mas a conta pedida dá 3 ÷ 0,015 = 200 Ω.'],
'el5:3':['Sobe um pouco, porque o resistor esquenta','Mais resistência sempre segura mais a corrente: 9 ÷ 900 = 10 mA, metade de antes.'],
'el5:4':['Ohm (Ω)','Ohm mede resistência. A corrente se mede em ampères.'],
'el6:1':['A preta no + e a vermelha encostada na mesa','Com uma ponta fora do circuito, não há o que medir. Vermelha no + e preta no −.'],
'el6:2':['Boa, porque toda bateria de 9 V marca menos do que 9 V','Nova, ela marca uns 9,5 V. Com 6,8 V está fraca, perto de acabar.'],
'el6:4':['Em paralelo, igual a quando se mede tensão','Tensão é em paralelo. Para corrente, a corrente precisa atravessar o aparelho: em série.'],
'el7:1':['Transforma a corrente da tomada em corrente de pilha','Quem faz isso é a fonte. O capacitor guarda um pouco de energia e solta logo depois.'],
'el7:3':['O LED esfria devagar e continua brilhando','LED não brilha por calor. A energia que manteve o LED aceso veio do capacitor.'],
'el7:4':['Só os capacitores grandes têm lado certo','Todo eletrolítico tem polaridade, do menor ao maior. A faixa − marca a perna negativa.'],
'el8:1':['O motor gira ao contrário se for ligado direto','O sentido não muda. O problema é a corrente: o motor puxa muito mais do que o pino aguenta.'],
'el8:2':['Um capacitor que guarda o sinal do Arduino','Ele não guarda nada: é um interruptor que um sinal fraco liga e desliga.'],
'el8:4':['Gira devagar, só com a energia da bateria','Sem sinal na base, o transistor corta o caminho e nenhuma corrente chega no motor.'],
'el9:3':['A tensão da bateria dobra e queima os LEDs','A tensão não dobra. O perigo é a corrente enorme, que esquenta fios e fonte.'],
'el10:0':['O potenciômetro, quando gira até o fim','O potenciômetro só muda o brilho. Quem abre e fecha o caminho é o botão.'],
'el10:1':['300 Ω exatos, mesmo que a loja não venda','300 Ω não é um valor de loja. Usa-se o mais perto e um pouco acima: 330 Ω.'],
'el10:2':['O resistor em paralelo com o LED, para dividir a corrente','Em paralelo o resistor não protege o LED. Tudo fica em série, num caminho só.'],
'rd2:0':['6 fios: 3 para enviar e 3 para receber','São 8 fios, em 4 pares trançados.'],
'rd2:1':['Para o cabo ficar mais forte e não quebrar','A trança não é para resistência: ela cancela a interferência entre os fios.'],
'rd2:4':['Funciona, desde que a capa seja da mesma cor','A cor da capa não importa. As duas pontas precisam seguir o mesmo padrão de fios.'],
'rd3:3':['Pelo modem, que também manda sinal de celular','O modem recebe a fibra. Quem cria o Wi-Fi para o celular é o roteador.'],
'rd3:4':['O modem é para cabo e o roteador é para Wi-Fi','O roteador também tem portas de cabo. O modem traz a internet; o roteador divide e cria o Wi-Fi.'],
'rd4:0':['O nome que aparece na lista de redes Wi-Fi','Esse é o nome da rede (SSID). O IP é o endereço de cada aparelho.'],
'rd4:1':['O modem, que recebe os IPs da operadora','O modem traz a internet. Dentro de casa, quem distribui os IPs é o roteador (DHCP).'],
'rd4:3':['O primeiro computador que foi ligado','O .1 fica reservado para o roteador, não para o primeiro aparelho.'],
'rd5:1':['Muitas pessoas usando o celular perto do roteador','Muitas pessoas dividem a velocidade, mas o que bloqueia o sinal são paredes, metal, espelhos e micro-ondas.'],
'rd5:2':['5 GHz alcança mais longe, mas é mais lenta','É o contrário: 5 GHz é rápida e alcança menos; 2,4 GHz alcança mais.'],
'rd5:3':['Porque o calor do chão estraga o roteador','O chão não esquenta o roteador. No alto o sinal passa por cima dos móveis.'],
'rd6:1':['Deixar a internet mais rápida para todos','O switch não aumenta a internet. Ele multiplica as portas da rede.'],
'rd6:4':['O roteador é para Wi-Fi e o switch é para cabo','O roteador também tem cabo. A diferença é que ele liga a rede à internet; o switch só liga aparelhos na mesma rede.'],
'rd7:0':['PC → modem → roteador → servidor do site','O roteador vem antes do modem, e entre o modem e o servidor há a internet.'],
'rd7:2':['O modem, que traduz a fibra','O modem só traz a internet. Quem traduz nomes em IPs é o DNS.'],
'rd7:3':['Num fluxo contínuo, como a água num cano','A rede corta tudo em pacotes pequenos, que podem ir por caminhos diferentes.'],
'rd8:1':['Ligar para a operadora e pedir um técnico','Antes de chamar alguém, confira luzes e cabos: é o problema mais comum.'],
'rd8:3':['No celular, que precisa ser formatado','Formatar é exagero. Reconectar ou reiniciar o roteador resolve na maioria das vezes.'],
'rd8:4':['Ele troca a senha do Wi-Fi sozinho','A senha continua a mesma. Reiniciar só limpa a memória e refaz as conexões.'],
'rd9:0':['Uma palavra difícil, como Paralelepipedo','Palavra única, mesmo difícil, está em dicionários usados por invasores. Frase longa com números e símbolos é mais segura.'],
'rd9:1':['Fazer as visitas gastarem menos internet','A rede de visitantes não limita o uso: ela separa as visitas dos seus aparelhos.'],
'rd9:2':['Esconde o nome da rede Wi-Fi','Esconder o nome é outra configuração. O firewall barra conexões suspeitas.'],
'rd9:3':['Desligar o roteador toda noite','Desligar não protege o painel. O importante é trocar a senha de fábrica.'],
'rd9:4':['WEP, porque é compatível com todos os aparelhos','O WEP é antigo e pode ser quebrado em minutos. Use WPA2 ou WPA3.'],
'rd10:0':['Um roteador para cada PC','Um roteador só basta. Para ligar vários PCs por cabo, usa-se um switch.'],
'rd10:2':['Uma rede só, com senha forte para todos','Senha forte ajuda, mas com todos na mesma rede os alunos enxergariam os computadores da secretaria.'],
'rd10:4':['Com Wi-Fi comum, apontando o roteador para o prédio','O Wi-Fi comum não alcança bem 150 m com paredes no caminho. O certo é a fibra óptica.']};
for(const [k,[t,fb]] of Object.entries(EXTRA)){const [id,i]=k.split(':');const s=PH[id]&&PH[id].steps[+i];if(s&&s.opts)s.opts.push({t,fb});}


/* ---------- animações simples ---------- */
const tweens=[];
function tween(o,to,dur){const fr={x:o.position.x,y:o.position.y,z:o.position.z,ry:o.rotation.y};tweens.push({o,fr,to,t:0,dur:reduceMotion?.01:dur});}
function stepTweens(dt){for(let i=tweens.length-1;i>=0;i--){const w=tweens[i];w.t=Math.min(1,w.t+dt/w.dur);const k=1-Math.pow(1-w.t,3);
  for(const a of ['x','y','z'])if(w.to[a]!=null)w.o.position[a]=w.fr[a]+(w.to[a]-w.fr[a])*k;if(w.to.ry!=null)w.o.rotation.y=w.fr.ry+(w.to.ry-w.fr.ry)*k;if(w.t>=1)tweens.splice(i,1);}}

/* ---------- estado da fase ---------- */
let G=null;
const panel=$('#panel');
function openPhase(id){if(/R\d$/.test(id))prepReview(id);const ph=PH[id];if(!ph)return;idleSim=null;if(ph.track)VIEW=ph.track;
  bench.parent&&scene.remove(bench);bench=new THREE.Group();scene.add(bench);for(const k in R)delete R[k];tweens.length=0;
  R.updaters=[];ph.build();bench.traverse(o=>{if(o.isMesh&&!(o.material&&o.material.transparent&&o.material.opacity<.5)){o.castShadow=true;o.receiveShadow=true;}});G={id,ph,step:0,err:0,hints:0,fb:null,locked:false,prog:[],sim:null,hintOn:false,wrongShown:{}};setOrd();
  const tr=TRACKS.find(t=>t.id===ph.track);const col=tr?tr.c:ph.c;document.body.style.setProperty('--c',col);
  $('#hudTrack').textContent=tr?(ph.rev?`${tr.short} · ${ph.final?'Desafio':'Revisão'}`:`${tr.short} · Fase ${ROMAN[ph.n-1]}`):'Fase 0';$('#hudTitle').textContent=ph.title;
  $('#map').style.display='none';$('#hud').style.display='flex';panel.style.display='block';$('#result').style.display='none';
  resetView();renderStep();}
function backToMap(){if(CAM.on)arOff();G=null;$('#map').style.display='block';$('#hud').style.display='none';panel.style.display='none';$('#result').style.display='none';drawMap();}
$('#backBtn').onclick=backToMap;
function resetView(){const mob=innerWidth<760;camera.position.set(0,mob?6.4:3.9,mob?6.4:4.6);controls.target.set(0,0,mob?.35:.25);controls.update();}

function dotsHud(){const n=G.ph.steps.length;$('#hudSteps').innerHTML=G.ph.steps.map((_,i)=>`<i class="${i<G.step?'done':i===G.step?'on':''}"></i>`).join('');}
function renderStep(){if(!G)return;dotsHud();const s=G.ph.steps[G.step];let h=say(s.g,s.say);
  if(G.hintOn&&s.hint)h+=say(s.g==='ar'?'lu':'ar',s.hint,'Dica');
  h+=`<div class="task">${s.task}</div>`;
  if(G.fb){const body=G.fb[1].replace(/^Isso!\s*/,'').replace(/<b>/g,'<strong>').replace(/<\/b>/g,'</strong>');h+=`<div class="fb ${G.fb[0]}"><b>${G.fb[0]==='good'?'Isso!':'Ops!'}</b>${body}</div>`;}
  if(G.locked){h+=`<button class="cta" id="nextBtn">${G.step<G.ph.steps.length-1?'Continuar':'Concluir fase'}</button>`;}
  else if(s.k==='info')h+=`<button class="cta" id="nextBtn">Continuar</button>`;
  else if(s.k==='choose')h+=`<div class="opts">${(G.ord||s.opts.map((_,i)=>i)).map(i=>{const o=s.opts[i];return `<button class="opt ${G.wrongShown[i]?'bad':''}" data-o="${i}">${o.t}${o.s?`<small>${o.s}</small>`:''}</button>`;}).join('')}</div>`;
  else if(s.k==='tap')h+=`<p class="tip">${CAM.on?'Toque na peça na tela. Arraste com um dedo para girar.':'Toque na peça na bancada. Arraste para girar e use dois dedos para dar zoom.'}</p>`;
  else if(s.k==='ar')h+=CAM.on?`<p class="tip">Procurando o marcador… A folha inteira precisa aparecer na tela.</p>`:`<button class="cta" id="arGo">Ligar a RA</button><button class="ghost" id="arSkip">Estou sem o marcador agora</button>`;
  else if(s.k==='code'){const pal=s.palette;const byId=Object.fromEntries(pal.map(b=>[b.id,b]));
    h+=`<div class="palette">${pal.map(b=>`<button class="blk ${b.c}" data-b="${b.id}">+ ${b.t}</button>`).join('')}</div>`;
    h+=`<div class="code">${G.prog.length?G.prog.map((id,i)=>`<div class="ln"><em>${i+1}</em><button class="blk ${byId[id].c}" data-rm="${i}">${byId[id].t}<span class="x">×</span></button></div>`).join(''):'<div class="empty">Toque nos blocos acima para montar o programa.</div>'}</div>`;
    h+=`<p class="loop">↻ repete para sempre</p><div class="row"><button class="ghost" id="clr" ${G.sim?'disabled':''}>Limpar</button><button class="cta" id="run" ${G.prog.length&&!G.sim?'':'disabled'}>${G.sim?'Rodando…':'▶ Rodar'}</button></div>`;}
  panel.innerHTML=h;panel.scrollTop=0;
  const nb=$('#nextBtn');if(nb)nb.onclick=next;
  panel.querySelectorAll('[data-o]').forEach(b=>b.onclick=()=>choose(+b.dataset.o));
  const ag=$('#arGo');if(ag)ag.onclick=arOn;const sk=$('#arSkip');if(sk)sk.onclick=()=>{good('Sem problema! Sem o marcador o jogo funciona aqui na tela. Quando tiver a folha impressa, toque em <b>Ligar RA</b> no topo.');};
  panel.querySelectorAll('[data-b]').forEach(b=>b.onclick=()=>{if(G.sim||G.prog.length>=s.max)return;G.prog.push(b.dataset.b);G.fb=null;renderStep();});
  panel.querySelectorAll('[data-rm]').forEach(b=>b.onclick=()=>{if(G.sim)return;G.prog.splice(+b.dataset.rm,1);renderStep();});
  const cl=$('#clr');if(cl)cl.onclick=()=>{G.prog=[];G.fb=null;renderStep();};const rn=$('#run');if(rn)rn.onclick=runCode;
  setGlow(s.k==='tap'&&!G.locked?(s.glow||[]):[]);viewOffset(true);}
function good(t){G.fb=['good',t];G.locked=true;const s=G.ph.steps[G.step];if(s.after)s.after();renderStep();}
function bad(t){G.err++;G.fb=['bad',t];renderStep();}
function next(){if(G.step<G.ph.steps.length-1){G.step++;G.fb=null;G.locked=false;G.prog=[];G.hintOn=false;G.wrongShown={};setOrd();renderStep();}else finish();}
function choose(i){const s=G.ph.steps[G.step];if(G.locked)return;const o=s.opts[i];if(o.ok)good(o.fb);else{G.wrongShown[i]=1;bad(o.fb);}}
function tapped(id){if(!G||G.locked)return;const s=G.ph.steps[G.step];if(s.k!=='tap')return;
  if([].concat(s.ok).includes(id)){good(s.fb);return;}
  const msg=(s.wrong&&s.wrong[id])||(NAMES[id]?`${NAMES[id].startsWith('a ')?'Essa':'Esse'} é ${NAMES[id]}. ${s.hint||''}`:'Aí não tem nada para tocar.');
  if(NAMES[id]&&G.ph.steps.some(x=>x.ok===id&&x.after))showLabel(id,NAMES[id].slice(2)[0].toUpperCase()+NAMES[id].slice(3));bad(msg);}
$('#hintBtn').onclick=()=>{if(!G)return;const s=G.ph.steps[G.step];if(!s.hint||G.locked){toast('Nesta etapa é só ler e continuar.');return;}if(!G.hintOn){G.hintOn=true;G.hints++;}renderStep();};

/* código: confere e simula no 3D */
function runCode(){const s=G.ph.steps[G.step];const [ok,msg]=s.check(G.prog);G.sim={prog:G.prog.slice(),t:0,ok,msg,dur:G.id==='rb3'?6.5:4.2};renderStep();}
function stepSim(dt){const m=G&&G.sim;if(!m)return;m.t+=dt;const p=m.prog;
  const scale=G.id==='rb3'?.45:.5;const seq=[];let tt=0;for(const b of p){if(b[0]==='w'){tt+=(+b.slice(1))*scale;}else seq.push([tt,b]);}const loop=Math.max(tt,.06);
  const now=m.t%loop;let state=null;const noWait=tt===0;
  if(G.id==='rb2'){let on=false;for(const [t0,b] of seq){if(t0<=now)on=b==='on';}
    if(noWait)on=p.includes('on');if(seq.length&&!seq.some(([t0])=>t0<=now))on=seq[seq.length-1][1]==='on';R.led.userData.set(on);}
  else{let cur=null;for(const [t0,b] of seq)if(t0<=now)cur=b;if(!cur&&seq.length)cur=seq[seq.length-1][1];if(noWait)cur=null;
    for(const k of ['r','y','g']){const on=noWait?p.includes(k):cur===k;R.leds[k].userData.set(on);const lc=new THREE.Color(R.leds[k].userData.color);R.lamps[k].material.emissive.copy(lc).multiplyScalar(on?1:.06);}}
  if(m.t>=m.dur){G.sim=null;if(m.ok){G.sim=null;good(m.msg);keepSim(m.prog);}else{lightsOff();bad(m.msg);}}}
let idleSim=null;function keepSim(p){idleSim={prog:p,t:0};}
function lightsOff(){if(R.led)R.led.userData.set(false);if(R.leds)for(const k in R.leds){R.leds[k].userData.set(false);const lc=new THREE.Color(R.leds[k].userData.color);R.lamps[k].material.emissive.copy(lc).multiplyScalar(.06);}}

/* ---------- fim da fase ---------- */
function finish(){const tot=G.err+G.hints;const st=tot===0?3:tot<=2?2:1;const id=G.id;P.done[id]=Math.max(P.done[id]||0,st);save();
  const ph=G.ph;const tr=TRACKS.find(t=>t.id===ph.track);let nextId=null,nextName='';if(tr){const sq=seqOf(tr);const ix=sq.findIndex(x=>x.id===id);const nx=sq[ix+1];if(nx&&nx.ready){nextId=nx.id;nextName=nx.rev?nx.name:`${ROMAN[nx.n-1]} · ${nx.name}`;}}
  $('#rcard').innerHTML=`<div class="big">${[1,2,3].map(i=>starSVG(i<=st,'pop')).join('')}</div><h2>Fase concluída!</h2><p>${st===3?'Perfeito, sem erros!':st===2?`${tot} ${tot===1?'erro ou dica':'erros ou dicas'}. Refaça para ganhar 3 estrelas.`:'Você conseguiu! Refaça para ganhar mais estrelas.'}</p>
    <div class="learn"><b>O que você aprendeu</b><ul>${ph.learned.map(x=>`<li>${x}</li>`).join('')}</ul></div>
    ${nextId?`<button class="cta" id="rNext">Continuar: ${nextName}</button>`:''}<button class="${nextId?'ghost':'cta'}" id="rMap">Voltar ao mapa</button><button class="ghost" id="rAgain">Refazer fase</button>`;
  $('#rcard').querySelectorAll('.big svg').forEach((s,i)=>s.style.animationDelay=(i*.15)+'s');
  $('#result').style.display='grid';const rn=$('#rNext');if(rn)rn.onclick=()=>openPhase(nextId);$('#rMap').onclick=backToMap;$('#rAgain').onclick=()=>openPhase(id);}

/* ---------- toque nas peças ---------- */
const ray=new THREE.Raycaster();let down=null;
renderer.domElement.addEventListener('pointerdown',e=>{down=[e.clientX,e.clientY,performance.now()];});
renderer.domElement.addEventListener('pointerup',e=>{if(!down||!G)return;const mv=Math.hypot(e.clientX-down[0],e.clientY-down[1]);const dt=performance.now()-down[2];down=null;if(mv>9||dt>600)return;
  if(CAM.on&&performance.now()-CAM.seen>500){toast('Aponte para o marcador para ver a bancada.');return;}
  const r=renderer.domElement.getBoundingClientRect();ray.setFromCamera({x:(e.clientX-r.left)/r.width*2-1,y:-(e.clientY-r.top)/r.height*2+1},camera);
  const hits=ray.intersectObjects(bench.children,true);for(const h of hits){if(h.object.isSprite||h.object.userData.noPick)continue;let o=h.object;while(o&&!o.userData.id&&o!==bench)o=o.parent;if(o&&o.userData.id&&o.visible!==false){tapped(o.userData.id);return;}}});

/* brilho nas áreas de toque */
let glowing=[];
function setGlow(ids){glowing.forEach(m=>{if(m.userData.e0!=null){m.material.emissive.setHex(m.userData.e0);m.material.emissiveIntensity=m.userData.ei0;}});glowing=[];
  for(const id of ids){const o=R[id];if(!o)continue;o.traverse(m=>{if(m.isMesh&&m.material&&!Array.isArray(m.material)&&m.material.emissive&&!m.material.transparent){if(m.userData.e0==null){m.userData.e0=m.material.emissive.getHex();m.userData.ei0=m.material.emissiveIntensity;}glowing.push(m);}});}}

/* ---------- RA (câmera + marcador) ---------- */
async function arOn(){const b=$('#arBtn');b.disabled=true;$('#arLabel').textContent='Abrindo…';const r=await camOpen();b.disabled=false;
  if(r!=='ok'){$('#arLabel').textContent='Ligar RA';toast(CAMERR[r],8000);return;}
  CAM.on=true;CAM.has=false;CAM.found=0;CAM.uYaw=0;CAM.uScale=1;controls.enabled=false;env.visible=false;shadowCatch.visible=true;scene.background=null;camera.clearViewOffset();vOff=null;camFov();
  b.classList.add('on');$('#arLabel').textContent='RA ligada';renderStep();}
function arOff(){if(video.srcObject){video.srcObject.getTracks().forEach(t=>t.stop());video.srcObject=null;}video.style.display='none';CAM.on=false;controls.enabled=true;env.visible=true;shadowCatch.visible=false;scene.background=BG;bench.visible=true;
  $('#arBtn').classList.remove('on');$('#arLabel').textContent='Ligar RA';$('#arMsg').style.display='none';camera.fov=45;camera.updateProjectionMatrix();resetView();if(G)renderStep();}
$('#arBtn').onclick=()=>CAM.on?arOff():arOn();

/* ---------- tela e laço ---------- */
let vOff=null;
function viewOffset(force){const W=innerWidth,H=innerHeight;let off=0;
  let offX=0;if(!CAM.on&&panel.style.display!=='none'){if(W<760){const top=panel.getBoundingClientRect().top;off=Math.max(0,Math.round((H-top)/2-24));}else offX=Math.round((panel.offsetWidth+16)/2);}
  const key=off+','+offX;if(key!==vOff||force){vOff=key;if(off||offX)camera.setViewOffset(W,H,offX,off,W,H);else camera.clearViewOffset();}}
let wasMob=innerWidth<760;
function resize(){renderer.setSize(innerWidth,innerHeight);camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();vOff=null;if(CAM.on)camFov();
  const mob=innerWidth<760;if(mob!==wasMob){wasMob=mob;if(!CAM.on)resetView();}}
addEventListener('resize',resize);resize();
function toast(t,ms=4500){const el=$('#toast');el.textContent=t;el.style.display='block';clearTimeout(toast.t);toast.t=setTimeout(()=>el.style.display='none',ms);}
const clock=new THREE.Clock();let fr=0;
function loop(){requestAnimationFrame(loop);const raw=Math.min(clock.getDelta(),.5),dt=Math.min(raw,.05),t=clock.elapsedTime;fr++;
  stepTweens(dt);
  if(CAM.on){camStep();const seen=performance.now()-CAM.seen<500;bench.visible=seen;const m=$('#arMsg');m.style.display=seen?'none':'block';m.textContent='Aponte a câmera para o marcador DesmontAR';
    if(G&&!G.locked&&G.ph.steps[G.step].k==='ar'&&CAM.found>0)good('A câmera achou os 4 cantos, leu os quadradinhos e calculou de onde você está olhando. Mova o celular em volta: o objeto fica preso à folha.');}
  else{controls.update();if(fr%20===0)viewOffset();}
  if(R.spin){R.spin.rotation.y+=dt*.8;R.spin.position.y=.6+Math.sin(t*2)*.06;}
  if(R.cooler&&R.cooler.userData.fan)R.cooler.userData.fan.rotation.y+=dt*9;
  const pulse=.3+.3*Math.sin(t*5);glowing.forEach(m=>{m.material.emissiveIntensity=1;m.material.emissive.setRGB(pulse*.96,pulse*.77,pulse*.1);});
  if(R.updaters)R.updaters.forEach(f=>f(dt,t));
  if(G&&G.sim)stepSim(raw);else if(idleSim&&G){idleSim.t+=raw;G.sim={prog:idleSim.prog,t:idleSim.t,dur:1e9,ok:1};stepSim(0);G.sim=null;}
  renderer.render(scene,camera);}
drawMap();loop();
window.__d2={openPhase,PH,G:()=>G,tapped,R,camera,THREE};
})();
