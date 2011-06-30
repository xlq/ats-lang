// simple pass-through shader
uniform mat4 mvp;
attribute vec4 pos;
attribute vec2 texcoord;
varying vec2 v_tc;

void main() {
  v_tc = texcoord;
  gl_Position = mvp * pos;
}
