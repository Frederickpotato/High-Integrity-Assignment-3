--  =====================================================================
--  SWEN90010 Assignment 3 — main.adb
--  Authors: Marlon Paththamperuma 1173217, <NAME 2> (<student ID>)
--  =====================================================================
--
--  TASK 1 — Code understanding (written answers below; no code changes)
--
--  Q1. Why does Spatial define separate Position and Velocity types,
--      both derived from Vector.Vector?
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

--  Q2. Several procedures in universe.ads have preconditions.
--      For each one, explain why it is needed and what runtime
--      error could occur if it were removed.
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
--  ---------------------------------------------------------------------
--  Provided simulation driver (Tasks 2–3 verification, Task 4 extension)
--  ---------------------------------------------------------------------
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

   --  -----------------------------------------------------------------
   --  TASK 4 — Collision-freedom proofs (Section 3.4)
   --  -----------------------------------------------------------------

   --  Task 4 (3.4): expected position at the current tick, derived from
   --  the position/velocity captured at the most recent bounce (or
   --  simulation start) plus velocity * Tick_Count.
   function Expected_Position (Item : Integer) return Spatial.Position is
     (Spatial.To_Position
        (Vector.Add
           (Spatial.To_Vector (Initial_Positions (Item)),
            Vector.Scale
              (Spatial.Vel_To_Vector (Initial_Velocities (Item)),
               Tick_Count))))
     with Pre => Item in 1 .. 2;

   --  Task 4 (3.4): position invariant used in the main loop and by gnatprove.
   function Position_Invariant (U : Univ.Universe) return Boolean is
     (Univ.Item_Count (U) = 2
      and then Tick_Count >= To_Big_Real (0)
      and then (for all I in 1 .. 2 =>
                  Univ.Get_Position (U, I) = Expected_Position (I)
                  and then Univ.Get_Velocity (U, I) = Initial_Velocities (I)
                  and then Univ.Get_Radius (U, I) = Initial_Radii (I)));

   --  Task 4 (3.4): helper — squared distance between two items.
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

   --  Task 4 (3.4): helper — squared minimum separation for a pair.
   function Pair_Sep2
     (I, J : Integer) return Big_Real is
       ((Initial_Radii (I) + Initial_Radii (J)) *
        (Initial_Radii (I) + Initial_Radii (J))) with
      Pre => I in 1 .. 2 and then J in 1 .. 2;

   --  Task 5 : TODO — collision check for one pair based on Collision_Math.
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
   --
   --  What each input means:
   --    S    = initial relative position (item I minus item J)
   --    V    = relative velocity (item I minus item J)
   --    Eps2 = squared collision threshold from pair radii

    --  Task 6.1 skeleton — soundness lemma for one pair.
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
         P1 : constant Vector.Vector := -- current position of item I as a vector
            Spatial.To_Vector (Univ.Get_Position (U, I));
         P2 : constant Vector.Vector := -- current position of item J as a vector
            Spatial.To_Vector (Univ.Get_Position (U, J));
         Init1 : constant Vector.Vector := -- initial position of item I as a vector
            Spatial.To_Vector (Initial_Positions (I));
         Init2 : constant Vector.Vector := -- initial position of item J as a vector
            Spatial.To_Vector (Initial_Positions (J));
         Vel1 : constant Vector.Vector := -- velocity of item I as a vector
            Spatial.Vel_To_Vector (Initial_Velocities (I));
         Vel2 : constant Vector.Vector := -- velocity of item J as a vector
            Spatial.Vel_To_Vector (Initial_Velocities (J));
         S : constant Vector.Vector := Vector.Sub (Init1, Init2); -- initial relative position
         V : constant Vector.Vector := Vector.Sub (Vel1, Vel2); -- relative velocity
         Eps2 : constant Big_Real := Pair_Sep2 (I, J);
    begin
             --  Current positions are linear evolution from the baseline state.
             pragma Assert
                (P1 = Vector.Add (Init1, Vector.Scale (Vel1, Tick_Count))); -- expected position from initial + velocity * time
             pragma Assert
                (P2 = Vector.Add (Init2, Vector.Scale (Vel2, Tick_Count))); -- expected position from initial + velocity * time

             --  Bridge current squared distance to vector-level distance at T.
             Collision_Math.Lemma_Sq_Dist_Bridge 
                (P1, P2, Init1, Init2, Vel1, Vel2, Tick_Count);

             --  Convert the pair predicate into the theorem precondition.
             pragma Assert (not Collision_Math.Will_Collide_Vec (S, V, Eps2));

             --  Apply soundness theorem: no future collision => strict separation.
             Collision_Math.Check_Implies_Safe_Vec (S, V, Eps2, Tick_Count);

             --  Link theorem result back to Squared_Dist helper used in main.
             pragma Assert
                (Vector.Dot (Vector.Sub (P1, P2), Vector.Sub (P1, P2)) =
                     Squared_Dist (U, I, J));
             pragma Assert
                (Squared_Dist (U, I, J) =
                     Collision_Math.Sq_Dist_At_Vec (S, V, Tick_Count));
    end Lemma_No_Collision_Pair;

   --  Provided — wall-bounce detection (not part of your Task 4 proof).
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
       Post =>
         Univ.Item_Count (U) = 2
         and then Tick_Count = To_Big_Real (0)
         and then (for all I in 1 .. 2 =>
                     Univ.Get_Position (U, I) = Initial_Positions (I)
                     and then Univ.Get_Velocity (U, I) = Initial_Velocities (I)
                     and then Univ.Get_Radius (U, I) = Initial_Radii (I))
         and then Position_Invariant (U);

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

   --  -----------------------------------------------------------------
   --  Main simulation loop
   --  Uses Task 2 (Init/Add_Item) and Task 3 (Tick) via Univ.Tick below.
   --  Task 4 TODOs: pre-loop check, in-loop assert, post-bounce check.
   --  -----------------------------------------------------------------
   

begin
   Reset_Universe;


   if not No_Future_Collision_Pair (1, 2) then --Collision check before the loop starts. If it does abort
      return;
   end if;

   for Frame in 1 .. 5000 loop
      pragma Loop_Invariant (Univ.Item_Count (U) = 2); -- The number of items in the universe should always be 2
      pragma Loop_Invariant (Tick_Count >= To_Big_Real (0));-- The tick count should always be non-negative
      pragma Loop_Invariant (Position_Invariant (U)); 
      pragma Loop_Invariant (No_Future_Collision_Pair (1, 2)); --Collision check for the loop invariant

      Lemma_No_Collision_Pair (U, 1, 2); --Collision check for the loop invariant using the lemma
      pragma Assert (Squared_Dist(U, 1, 2) > Pair_Sep2 (1, 2)); --Collision check for the assertion

  

      Disp.Capture (U);
      Univ.Tick (U);  --  Task 3 — advances every item one tick
      Tick_Count := Tick_Count + To_Big_Real (1);

      pragma Assert (Position_Invariant (U));
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

            if not No_Future_Collision_Pair (1, 2) then --Collision check after the bounce
               exit;
            end if;

            --  Task 4 (3.4): TODO — re-check after wall bounce + reset.
            --  TODO: add post-bounce collision check
            --  Task 5/6 guide:
            --    Re-establish ghost assumptions after reset (new initial
            --    position/velocity baseline) before continuing the loop.
         end if;
      end;
   end loop;

   --  Task 3 verification — build (alr build) and run (alr run) to produce
   --  simulation.html; open in a browser to compare with the reference.
   Disp.Capture (U);
   Disp.Save ("simulation.html",
              Arena_X_Min, Arena_X_Max,
              Arena_Y_Min, Arena_Y_Max);
   Ada.Text_IO.Put_Line ("Wrote simulation.html");
end Main;
