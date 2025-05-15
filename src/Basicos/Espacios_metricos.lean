-- ---------------------------------------------------------------------
-- Ejercicio 1. Ejecuta las siguientes acciones
-- 1. Importar la teoría de espacios métricos.
-- 2. Declarar X como un tipo sobre espacios métricos.
-- 3. Declarar x, y y z como variables sobre X.
-- ----------------------------------------------------------------------

import Mathlib.Topology.MetricSpace.Basic
variable {X : Type _} [MetricSpace X]
variable (x y z : X)

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo de las siguientes expresiones
--    dist_self x
--    dist_comm x y
--    dist_triangle x y z
-- ----------------------------------------------------------------------

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)
