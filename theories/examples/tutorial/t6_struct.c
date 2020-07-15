#include <stdint.h>

struct [[rc::refined_by("r : nat", "g : nat", "b : nat")]] color {
  [[rc::field("r @ int<u8>")]]
  uint8_t r;

  [[rc::field("g @ int<u8>")]]
  uint8_t g;

  [[rc::field("b @ int<u8>")]]
  uint8_t b;
};

[[rc::parameters("r : nat", "g : nat", "b : nat")]]
[[rc::args("r @ int<u8>", "g @ int<u8>","b @ int<u8>")]]
[[rc::returns("{(r, g, b)} @ color")]]
struct color rgb(uint8_t r, uint8_t g, uint8_t b) {
  return (struct color){ .r = r, .g = g, .b = b };
}

[[rc::parameters("r : nat")]]
[[rc::args("r @ int<u8>")]]
[[rc::returns("{(r, 0, 0)%nat} @ color")]]
struct color red(uint8_t r) {
  struct color c = { .r = r };
  return c;
}

[[rc::parameters("g : nat")]]
[[rc::args("g @ int<u8>")]]
[[rc::returns("{(0, g, 0)%nat} @ color")]]
struct color green(uint8_t g) {
  return (struct color) { .g = g };
}

[[rc::parameters("b : nat")]]
[[rc::args("b @ int<u8>")]]
[[rc::returns("{(0, 0, b)%nat} @ color")]]
struct color blue(uint8_t b) {
  struct color c;
  c = (struct color){ .b = b };
  return c;
}
