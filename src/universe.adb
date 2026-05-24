with Ada.Text_IO; with Ada.Integer_Text_IO;
--  Text output helpers used by Print.

package body Universe with SPARK_Mode is
   --  Package body for the generic Universe API.

   --  -----------------------------------------------------------------
   --  TASK 2 — Implement Init and Add_Item (Section 3.2)
   --  -----------------------------------------------------------------

   procedure Init (U : out Universe) is
      --  Reset every storage slot to zero values and clear active count.
   begin
      U := (items      => (others => (pos => Spatial.To_Position
                                        ((X => To_Big_Real (0),
                                          Y => To_Big_Real (0))),
                                      vel => Spatial.To_Velocity
                                        ((X => To_Big_Real (0),
                                          Y => To_Big_Real (0))),
                                      rad => To_Big_Real (0))),
            item_count => 0);
   end Init;

   procedure Add_Item
     (U   : in out Universe;
      pos : Spatial.Position;
      vel : Spatial.Velocity;
      rad : Big_Real)
   is
   begin
      --  Append one item at the end of the active prefix.
      U.item_count := U.item_count + 1;
      U.items (U.item_count) := (pos => pos, vel => vel, rad => rad);
   end Add_Item;

   procedure Reflect_Velocity_X
     (U : in out Universe; Index : Integer) is
   begin
      --  Wall bounce on X: negate only the X component.
      U.items (Index).vel := Spatial.Negate_Vel_X (U.items (Index).vel);
   end Reflect_Velocity_X;

   procedure Reflect_Velocity_Y
     (U : in out Universe; Index : Integer) is
   begin
      --  Wall bounce on Y: negate only the Y component.
      U.items (Index).vel := Spatial.Negate_Vel_Y (U.items (Index).vel);
   end Reflect_Velocity_Y;

   procedure Print (U : Universe)
     with SPARK_Mode => Off
   is
   begin
      --  Print positions for active items (debug utility only).
      for I in U.items'First .. U.item_count loop
         Ada.Text_IO.Put ("Item: ");
         Ada.Integer_Text_IO.Put (I);
         Ada.Text_IO.Put (": pos: (");
         Ada.Text_IO.Put
           (To_String (Spatial.Pos_X (U.items (I).pos)));
         Ada.Text_IO.Put (",");
         Ada.Text_IO.Put
           (To_String (Spatial.Pos_Y (U.items (I).pos)));
         Ada.Text_IO.Put (")");
         Ada.Text_IO.New_Line;
      end loop;
   end Print;

   --  -----------------------------------------------------------------
   --  TASK 3 — Implement Tick with loop invariants (Section 3.3)
   --  Verification: alr build && alr run → simulation.html
   --  -----------------------------------------------------------------

   procedure Tick (U : in out Universe) is
   begin
      for I in 1 .. U.item_count loop
         --  Active item count is preserved by Tick.
         pragma Loop_Invariant
           (Item_Count (U) = Item_Count (U'Loop_Entry));
         --  Items already visited were advanced exactly once.
         pragma Loop_Invariant
           (for all K in 1 .. I - 1 =>
              Get_Position (U, K) =
                Spatial.Move (Get_Position (U'Loop_Entry, K),
                              Get_Velocity (U'Loop_Entry, K)));
         --  Items not yet visited are still unchanged.
         pragma Loop_Invariant
           (for all K in I .. Item_Count (U) =>
              Get_Position (U, K) = Get_Position (U'Loop_Entry, K));
         --  Tick does not change velocity or radius.
         pragma Loop_Invariant
           (for all K in 1 .. Item_Count (U) =>
              Get_Velocity (U, K) = Get_Velocity (U'Loop_Entry, K)
              and then Get_Radius (U, K) = Get_Radius (U'Loop_Entry, K));

         --  One-step motion update: position := position + velocity.
         U.items (I).pos := Spatial.Move (U.items (I).pos, U.items (I).vel);
      end loop;
   end Tick;

end Universe;
