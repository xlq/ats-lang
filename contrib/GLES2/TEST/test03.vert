// simple pass-through shader
uniform mat4 mvp;
attribute vec4 pos;

void main() {
  gl_Position = mvp * pos;
}
