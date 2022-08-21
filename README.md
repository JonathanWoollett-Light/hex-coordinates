# hex-coordinates

[![crates.io](https://img.shields.io/crates/v/hex-coordinates)](https://crates.io/crates/hex-coordinates)
[![docs.rs](https://img.shields.io/docsrs/hex-coordinates)](https://docs.rs/hex-coordinates/)

A library for handling hex coordinates.

Massive credit to [Hexagonal Grids from Red Blob Games](https://www.redblobgames.com/grids/hexagons/).

<table class="grid-comparison"><thead><tr><th></th><th>Offset</th><th>Doubled</th><th>Axial</
th><th>Cube</th></tr></thead><tbody><tr><th>Pointy Rotation</th><td>evenr,
oddr</td><td>doublewidth</td><td rowspan="2">axial</td><td
rowspan="2">cube</td></tr><tr><th>Flat Rotation</th><td>evenq,
oddq</td><td>doubleheight</td></tr><tr><th>Other Rotations</th><td colspan="2">no</td><td
colspan="2">yes</td></tr><tr><th>Vector operations
(add,&nbsp;subtract,&nbsp;scale)</th><td>no</td><td>yes</td><td>yes</td><td>yes</td></
tr><tr><th>Array
storage</th><td>rectangular</td><td>no<sup>*</sup></td><td>rhombus<sup>*</sup></td><td>no<sup>*
</sup></td></tr><tr><th>Hash storage</th><td colspan="2">any shape</td><td colspan="2">any
shape</td></tr><tr><th>Hexagonal
symmetry</th><td>no</td><td>no</td><td>no</td><td>yes</td></tr><tr><th>Easy
algorithms</th><td>few</td><td>some</td><td>most</td><td>most</td></tr></tbody></table>

The article notes:
> My recommendation: if you are only going to use non-rotated rectangular maps, consider the
> doubled or offset system that matches your map orientation. For maps with Rotation, or
> non-rectangularly shaped maps, use axial/cube. Either choose to store the s coordinate (cube),
> or calculate it when needed as -q-r (axial).
