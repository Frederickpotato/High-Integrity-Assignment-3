--  Authors: Marlon Paththamperuma 1173217, Christopher Siang 1270328
--
--  TASK 1 — Code understanding
--
--  Q1:
--
--  Advantage:
--    Although Position and Velocity share the same underlying record
--    representation as Vector.Vector, Ada treats them as incompatible
--    types. A value of type Position cannot be passed where a Velocity
--    is expected, and vice versa, without an explicit casting. This means
--    the compiler enforces the physical distinction between "a location
--    in the arena" and "a rate of change per tick" throughout the
--    codebase
--
--  Kinds of errors prevented by having distinct types:
--    1.  Passing a position where a velocity is expected or vice
--        versa in any function call
--    2.  Accidentally assigning a position into a velocity variable
--        or the reverse, silently reinterpreting one physical
--        quantity as another.
--    3.  Mixing positions and velocities in arithmetic, for example,
--        adding a position to a velocity produces a meaningless result
--        physically, but would type-check if both were plain Vector.
--
--  Concrete compile-time example:
--    Suppose P : Position and V : Velocity. With plain Vector, the
--    following compiles silently but is physically wrong:
--    V := P;       assigns a position into a velocity slot
--    P := P + V;   adds without going through Spatial.Move
--
--    With distinct derived types, both lines are rejected at compile
--    time. The first because Position and Velocity are different types,
--    the second because "+" is not defined between Position and
--    Velocity

--  Q2:
--
--  Precondition 1: Index >= 1 and then Index <= Item_Count (U)
--    Used by: Get_Position, Get_Velocity, Get_Radius,
--              Reflect_Velocity_X, Reflect_Velocity_Y
--
--    These procedures look up an item by its index in the internal
--    array. The precondition ensures the index actually points to
--    a valid, populated slot.  Without it:
--      - If Index < 1, the array access crashes at runtime
--        (Ada raises Constraint_Error for out-of-range indices).
--      - If Index > Item_Count (U) but still <= Max_Items, Ada does
--        NOT crash, because the index is technically within the
--        array bounds.  However, that slot was never filled by
--        Add_Item -- it holds leftover initialisation data, not
--        a real object.  The procedure returns or modifies that
--        meaningless data silently, with no error, making the
--        bug very hard to detect.
--
--  Precondition 2: Item_Count (U) < Max_Items
--    Used by: Add_Item
--    Add_Item increments the item count and then writes into the
--    next slot.  Without this precondition, if the universe is
--    already full like Item_Count = Max_Items, the count would be
--    incremented past Max_Items and the write would go beyond the
--    end of the array. Both of these crash at runtime with
--    Constraint_Error. The precondition prevents Add_Item from
--    ever being called when there is no room left.
--    
--
--  Task 7: The proof does not show that an early halt will result in a future collision.
--  In the implementation in the main loop, future collisions are checked with No_Future_Collision_Pair
--  which uses the Will_collide_Vec predicate. It's called after a bounce is detected
-- and the universe is reset and at the initial stage of the universe. If it returns false, it comes to a halt.
--  Will_Collide_Vec is the provided predicate to check for future collisions but doesn't
--  verify that one or both items will collide with a wall before the future collision. So,
--  if the items are on a trajectory that would lead to a future collision but would've collided with a wall first,
--  the No_Future_Collision_Pair would be using the Will_Collide_Vec predicate to check for a future collision and 
--  return false and cause an early halt but a collision would not have occured in that trajectory
-- thus not proving a collision will definitely happen in the future.
--
with Universe;
with Spatial;
with Vector; use Vector;
with Collision_Math;
with Display;
with Ada.Text_IO;
with Ada.Numerics.Big_Numbers.Big_Reals;
use Ada.Numerics.Big_Numbers.Big_Reals;

procedure Main with SPARK_Mode is
   use type Spatial.Velocity;
   use type Spatial.Position;
   package Univ is new Universe (10);

   package FC is new Float_Conversions (Float);
   package Disp is new Display (Univ, Max_Frames => 5500);

   U : Univ.Universe;

   Arena_X_Min : constant Big_Real := FC.To_Big_Real (-100.0);
   Arena_X_Max : constant Big_Real := FC.To_Big_Real (100.0);
   Arena_Y_Min : constant Big_Real := FC.To_Big_Real (-50.0);
   Arena_Y_Max : constant Big_Real := FC.To_Big_Real (50.0);

   Initial_Positions : array (1 .. 2) of Spatial.Position :=
     (Spatial.To_Position
        ((X => FC.To_Big_Real (0.0), Y => FC.To_Big_Real (5.0))),
      Spatial.To_Position
        ((X => FC.To_Big_Real (0.0), Y => FC.To_Big_Real (-5.0))));

   Initial_Velocities : array (1 .. 2) of Spatial.Velocity :=
     (Spatial.To_Velocity
        ((X => FC.To_Big_Real (0.4), Y => FC.To_Big_Real (0.3))),
      Spatial.To_Velocity
        ((X => FC.To_Big_Real (1.0), Y => FC.To_Big_Real (-0.7))));

   Initial_Radii : constant array (1 .. 2) of Big_Real :=
     (FC.To_Big_Real (2.0), FC.To_Big_Real (2.0));

   Tick_Count : Big_Real := To_Big_Real (0);

   -- Expected_Position is a helper function for the Position Invariant
   function Expected_Position (Item : Integer) return Spatial.Position is
     (Spatial.To_Position
        (Vector.Add
           (Spatial.To_Vector (Initial_Positions (Item)),
            Vector.Scale(Spatial.Vel_To_Vector (Initial_Velocities (Item)), 
                        Tick_Count))))
     with Pre => Item in 1 .. 2;

   --  Task 4 Define Position Invariant
   function Position_Invariant (U : Univ.Universe) return Boolean is
     (Univ.Item_Count (U) = 2
      and then Tick_Count >= To_Big_Real (0)
      and then (for all I in 1 .. 2 =>
                  Univ.Get_Position (U, I) = Expected_Position (I)
                  and then Univ.Get_Velocity (U, I) = Initial_Velocities (I)
                  and then Univ.Get_Radius (U, I) = Initial_Radii (I)));

   function Squared_Dist
     (U : Univ.Universe; I, J : Integer) return Big_Real is
       (Vector.Dot
          (Vector.Sub
             (Spatial.To_Vector (Univ.Get_Position (U, I)),
              Spatial.To_Vector (Univ.Get_Position (U, J))),
           Vector.Sub
             (Spatial.To_Vector (Univ.Get_Position (U, I)),
              Spatial.To_Vector (Univ.Get_Position (U, J))))) with
      Pre => I >= 1 and then I <= Univ.Item_Count (U)
             and then J >= 1 and then J <= Univ.Item_Count (U);

   function Pair_Sep2
     (I, J : Integer) return Big_Real is
       ((Initial_Radii (I) + Initial_Radii (J)) *
        (Initial_Radii (I) + Initial_Radii (J))) with
      Pre => I in 1 .. 2 and then J in 1 .. 2;


   -- Task 5 - Define No_Future_Collision_Pair
   function No_Future_Collision_Pair (I, J : Integer) return Boolean is
      (not Collision_Math.Will_Collide_Vec
          (S    => Vector.Sub
                     (Spatial.To_Vector (Initial_Positions (I)),
                      Spatial.To_Vector (Initial_Positions (J))),
           V    => Vector.Sub
                     (Spatial.Vel_To_Vector (Initial_Velocities (I)),
                      Spatial.Vel_To_Vector (Initial_Velocities (J))),
           Eps2 => Pair_Sep2 (I, J)))
     with
       Pre => I in 1 .. 2 and then J in 1 .. 2;

    --  Task 6 - Define Lemma_No_Collision_Pair
    procedure Lemma_No_Collision_Pair
       (U : Univ.Universe; I, J : Integer)
    with
         Ghost,
         Pre  => Position_Invariant (U)
                     and then I in 1 .. 2
                     and then J in 1 .. 2
                     and then Tick_Count >= To_Big_Real (0)
                     and then No_Future_Collision_Pair (I, J), 
         Post => Squared_Dist (U, I, J) > Pair_Sep2 (I, J);

    procedure Lemma_No_Collision_Pair
       (U : Univ.Universe; I, J : Integer) is
         P1 : constant Vector.Vector :=
            Spatial.To_Vector (Univ.Get_Position (U, I));
         P2 : constant Vector.Vector :=
            Spatial.To_Vector (Univ.Get_Position (U, J));
         Init1 : constant Vector.Vector :=
            Spatial.To_Vector (Initial_Positions (I));
         Init2 : constant Vector.Vector :=
            Spatial.To_Vector (Initial_Positions (J));
         Vel1 : constant Vector.Vector :=
            Spatial.Vel_To_Vector (Initial_Velocities (I));
         Vel2 : constant Vector.Vector :=
            Spatial.Vel_To_Vector (Initial_Velocities (J));
         S : constant Vector.Vector := Vector.Sub (Init1, Init2);
         V : constant Vector.Vector := Vector.Sub (Vel1, Vel2);
         Eps2 : constant Big_Real := Pair_Sep2 (I, J);
    begin
             pragma Assert
                (P1 = Vector.Add (Init1, Vector.Scale (Vel1, Tick_Count)));
             pragma Assert
                (P2 = Vector.Add (Init2, Vector.Scale (Vel2, Tick_Count)));

             Collision_Math.Lemma_Sq_Dist_Bridge 
                (P1, P2, Init1, Init2, Vel1, Vel2, Tick_Count);

             pragma Assert (not Collision_Math.Will_Collide_Vec (S, V, Eps2));

             Collision_Math.Check_Implies_Safe_Vec (S, V, Eps2, Tick_Count);

             pragma Assert
                (Vector.Dot (Vector.Sub (P1, P2), Vector.Sub (P1, P2)) =
                     Squared_Dist (U, I, J));
             pragma Assert
                (Squared_Dist (U, I, J) =
                     Collision_Math.Sq_Dist_At_Vec (S, V, Tick_Count));
    end Lemma_No_Collision_Pair;

   type Bounce_Flags is record
      X : Boolean := False;
      Y : Boolean := False;
   end record;

   type Bounce_Array is array (1 .. 2) of Bounce_Flags;

   function Detect_Bounces
     (U : Univ.Universe) return Bounce_Array
     with Pre => Univ.Item_Count (U) = 2;

   function Detect_Bounces
     (U : Univ.Universe) return Bounce_Array
   is
      Result : Bounce_Array := (others => (X => False, Y => False));
   begin
      for Item in 1 .. 2 loop
         declare
            P : constant Spatial.Position :=
              Univ.Get_Position (U, Item);
            R : constant Big_Real := Univ.Get_Radius (U, Item);
         begin
            if Spatial.Pos_X (P) + R > Arena_X_Max
              or else Spatial.Pos_X (P) - R < Arena_X_Min
            then
               Result (Item).X := True;
            end if;
            if Spatial.Pos_Y (P) + R > Arena_Y_Max
              or else Spatial.Pos_Y (P) - R < Arena_Y_Min
            then
               Result (Item).Y := True;
            end if;
         end;
      end loop;
      return Result;
   end Detect_Bounces;

   procedure Print_Collision (Frame : Integer);

   procedure Print_Collision (Frame : Integer)
     with SPARK_Mode => Off
   is
   begin
      Ada.Text_IO.Put_Line
        ("Collision will occur after bounce at frame"
         & Integer'Image (Frame));
      for Item in 1 .. 2 loop
         declare
            V : constant Vector.Vector :=
              Spatial.Vel_To_Vector (Initial_Velocities (Item));
            P : constant Spatial.Position :=
              Initial_Positions (Item);
         begin
            Ada.Text_IO.Put_Line
              ("  Item" & Integer'Image (Item)
               & " pos=("
               & To_String (Spatial.Pos_X (P)) & ", "
               & To_String (Spatial.Pos_Y (P)) & ")"
               & " vel=("
               & To_String (V.X) & ", "
               & To_String (V.Y) & ")");
         end;
      end loop;
      Ada.Text_IO.Put_Line
        ("  Sep2=" & To_String (Pair_Sep2 (1, 2)));
   end Print_Collision;

   procedure Reset_Universe
     with
      --Task 4 PostConditions for Reset_Universe
       Post =>
         Univ.Item_Count (U) = 2
         and then Tick_Count = To_Big_Real (0)
         and then (for all I in 1 .. 2 =>
                     Univ.Get_Position (U, I) = Initial_Positions (I)
                     and then Univ.Get_Velocity (U, I) = Initial_Velocities (I)
                     and then Univ.Get_Radius (U, I) = Initial_Radii (I))
         and then Position_Invariant (U); -- Task 4 Adding Position Invariant to the PostConditions

   procedure Reset_Universe is
   begin
      Tick_Count := To_Big_Real (0);
      Univ.Init (U);
      Univ.Add_Item (U,
                     Initial_Positions (1),
                     Initial_Velocities (1),
                     Initial_Radii (1));
      Univ.Add_Item (U,
                     Initial_Positions (2),
                     Initial_Velocities (2),
                     Initial_Radii (2));
   end Reset_Universe;

begin
   Reset_Universe;

   if not No_Future_Collision_Pair (1, 2) then --Task 5 - Add collision check before the loop
      return;
   end if;

   for Frame in 1 .. 5000 loop
    -- Task 4 Adding Loop Invariants
      pragma Loop_Invariant (Univ.Item_Count (U) = 2); 
      pragma Loop_Invariant (Tick_Count >= To_Big_Real (0));
      pragma Loop_Invariant (Position_Invariant (U)); -- Task 4 Adding Position Invariant to the Loop Invariant
      pragma Loop_Invariant (No_Future_Collision_Pair (1, 2)); --Task 5 - Add collision check to the Loop Invariant

      Lemma_No_Collision_Pair (U, 1, 2); 
      pragma Assert (Squared_Dist(U, 1, 2) > Pair_Sep2 (1, 2)); 

  

      Disp.Capture (U);
      Univ.Tick (U);

      declare
         T  : constant Big_Real := Tick_Count;
         T1 : constant Big_Real := T + To_Big_Real (1);
      begin
         for I in 1 .. 2 loop
            pragma Loop_Invariant (Univ.Item_Count (U) = 2);
            pragma Loop_Invariant
              (for all K in I .. 2 =>
                 Spatial.To_Vector (Univ.Get_Position (U, K)) =
                   Vector.Add
                     (Spatial.To_Vector (Initial_Positions (K)),
                      Vector.Add
                        (Vector.Scale
                           (Spatial.Vel_To_Vector
                              (Initial_Velocities (K)), T),
                         Spatial.Vel_To_Vector
                           (Initial_Velocities (K)))));
            pragma Loop_Invariant
              (for all K in 1 .. I - 1 =>
                 Univ.Get_Position (U, K) =
                   Spatial.To_Position
                     (Vector.Add
                        (Spatial.To_Vector (Initial_Positions (K)),
                         Vector.Scale
                           (Spatial.Vel_To_Vector
                              (Initial_Velocities (K)), T1))));
            declare
               Init_V : constant Vector.Vector :=
                 Spatial.To_Vector (Initial_Positions (I));
               Vel_V  : constant Vector.Vector :=
                 Spatial.Vel_To_Vector (Initial_Velocities (I));
               Pos_V  : constant Vector.Vector :=
                 Spatial.To_Vector (Univ.Get_Position (U, I));
               Target : constant Vector.Vector :=
                 Vector.Add (Init_V, Vector.Scale (Vel_V, T1));
            begin
               pragma Assert (Pos_V.X = Init_V.X + Vel_V.X * T + Vel_V.X);
               pragma Assert (Pos_V.Y = Init_V.Y + Vel_V.Y * T + Vel_V.Y);
               pragma Assert (Pos_V.X = Init_V.X + Vel_V.X * T1);
               pragma Assert (Pos_V.Y = Init_V.Y + Vel_V.Y * T1);
               pragma Assert (Pos_V.X = Target.X);
               pragma Assert (Pos_V.Y = Target.Y);
               pragma Assert (Pos_V = Target);
               pragma Assert
                 (Univ.Get_Position (U, I) = Spatial.To_Position (Target));
            end;
         end loop;
      end;

      Tick_Count := Tick_Count + To_Big_Real (1);

      pragma Assert (Position_Invariant (U)); -- Task 4 Position_Invariant restored after Tick.
      declare
         Flags : constant Bounce_Array := Detect_Bounces (U);
      begin
         if Flags (1).X or else Flags (1).Y
           or else Flags (2).X or else Flags (2).Y
         then
            for Item in 1 .. 2 loop
               pragma Loop_Invariant (Univ.Item_Count (U) = 2);
               if Flags (Item).X then
                  Univ.Reflect_Velocity_X (U, Item);
               end if;
               if Flags (Item).Y then
                  Univ.Reflect_Velocity_Y (U, Item);
               end if;
            end loop;
            Initial_Positions :=
              (Univ.Get_Position (U, 1),
               Univ.Get_Position (U, 2));
            Initial_Velocities :=
              (Univ.Get_Velocity (U, 1),
               Univ.Get_Velocity (U, 2));

            Reset_Universe; 

            if not No_Future_Collision_Pair (1, 2) then --Task 5 - Add collision check 
               exit;
            end if;
         end if;
      end;
   end loop;

 
   Disp.Capture (U);
   Disp.Save ("simulation.html",
              Arena_X_Min, Arena_X_Max,
              Arena_Y_Min, Arena_Y_Max);
   Ada.Text_IO.Put_Line ("Wrote simulation.html");
end Main;
