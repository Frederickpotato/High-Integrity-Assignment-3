with Universe;
with Spatial;
with Vector; use Vector;
with Display;
with Ada.Text_IO;
with Ada.Numerics.Big_Numbers.Big_Reals;
use Ada.Numerics.Big_Numbers.Big_Reals;

procedure Main with SPARK_Mode is
   use type Spatial.Velocity;
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

   --  TODO: define Position_Invariant

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
      Pre => I in 1 .. 2 and J in 1 .. 2;

   --  TODO: define No_Future_Collision_Pair

   --  TODO: define Lemma_No_Collision_Pair

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
   --  TODO: add postcondition
   is
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

   --  TODO: add pre-loop collision check

   for Frame in 1 .. 5000 loop
      --  TODO: add loop invariants

      --  TODO: call soundness lemma and assert collision freedom

      Disp.Capture (U);
      Univ.Tick (U);
      Tick_Count := Tick_Count + To_Big_Real (1);

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

            --  TODO: add post-bounce collision check
         end if;
      end;
   end loop;

   Disp.Capture (U);
   Disp.Save ("simulation.html",
              Arena_X_Min, Arena_X_Max,
              Arena_Y_Min, Arena_Y_Max);
   Ada.Text_IO.Put_Line ("Wrote simulation.html");
end Main;
